const util = require('util');
const assert = require('assert');
const stdhttp = require('http');
const crypto = require('crypto');
const querystring = require('querystring');
const url = require('url');

const jose = require('@panva/jose');
const base64url = require('base64url');
const {
  defaultsDeep, isPlainObject, merge, defaults, omitBy,
} = require('lodash');
const tokenHash = require('oidc-token-hash');

const pick = require('./helpers/pick');
const errorHandlerFactory = require('./helpers/error_handler');
const processResponse = require('./helpers/process_response');
const TokenSet = require('./token_set');
const OpenIdConnectError = require('./open_id_connect_error');
const now = require('./util/unix_timestamp');
const { CALLBACK_PROPERTIES, CLIENT_DEFAULTS, JWT_CONTENT } = require('./helpers/consts');
const issuerRegistry = require('./issuer_registry');
const random = require('./util/random');
const instance = require('./helpers/weak_cache');

const errorHandler = errorHandlerFactory();
const bearerErrorHandler = errorHandlerFactory({ bearerEndpoint: true });

function pickCb(input) {
  return pick(input, ...CALLBACK_PROPERTIES);
}

function formUrlEncode(value) {
  return encodeURIComponent(value).replace(/%20/g, '+');
}

function bearer(token) {
  return `Bearer ${token}`;
}

function cleanUpClaims(claims) {
  if (Object.keys(claims._claim_names).length === 0) {
    delete claims._claim_names;
  }
  if (Object.keys(claims._claim_sources).length === 0) {
    delete claims._claim_sources;
  }
}

function assignClaim(target, source, sourceName) {
  return ([claim, inSource]) => {
    if (inSource === sourceName) {
      assert(source[claim] !== undefined, `expected claim "${claim}" in "${sourceName}"`);
      target[claim] = source[claim];
      delete target._claim_names[claim];
    }
  };
}

function getFromJWT(jwt, position, claim) {
  assert.strictEqual(typeof jwt, 'string', 'invalid JWT type, expected a string');
  const parts = jwt.split('.');
  assert.strictEqual(parts.length, 3, 'invalid JWT format, expected three parts');
  const parsed = JSON.parse(base64url.decode(parts[position]));
  return typeof claim === 'undefined' ? parsed : parsed[claim];
}

function getSub(jwt) {
  return getFromJWT(jwt, 1, 'sub');
}

function getIss(jwt) {
  return getFromJWT(jwt, 1, 'iss');
}

function getHeader(jwt) {
  return getFromJWT(jwt, 0);
}

function getPayload(jwt) {
  return getFromJWT(jwt, 1);
}

function verifyPresence(prop) {
  if (this[prop] === undefined) {
    throw new Error(`missing required JWT property ${prop}`);
  }
}

function authorizationParams(params) {
  assert(isPlainObject(params), 'pass a plain object as the first argument');

  const authParams = Object.assign(
    {
      client_id: this.client_id,
      scope: 'openid',
      response_type: this.resolveResponseType(),
      redirect_uri: this.resolvedRedirectUri(),
    },
    params,
  );

  Object.entries(authParams).forEach(([key, value]) => {
    if (value === null || value === undefined) {
      delete authParams[key];
    } else if (key === 'claims' && typeof value === 'object') {
      authParams[key] = JSON.stringify(value);
    } else if (typeof value !== 'string') {
      authParams[key] = String(value);
    }
  });

  assert(
    [undefined, 'none', 'code', 'token'].includes(authParams.response_type) || authParams.nonce,
    'nonce MUST be provided for implicit and hybrid flows',
  );

  return authParams;
}

async function claimJWT(jwt) {
  const iss = getIss(jwt);
  const keyDef = getHeader(jwt);
  assert(keyDef.alg, 'claim source is missing JWT header alg property');

  if (keyDef.alg === 'none') {
    return getPayload(jwt);
  }

  let key;
  if (!iss || iss === this.issuer.issuer) {
    key = await this.issuer.key(keyDef);
  } else if (issuerRegistry.has(iss)) {
    key = await issuerRegistry.get(iss).key(keyDef);
  } else {
    const discovered = await this.issuer.constructor.discover(iss);
    key = await discovered.key(keyDef);
  }

  return jose.JWS.verify(jwt, key);
}

function checkStore(keystore) {
  assert(keystore instanceof jose.JWKS.KeyStore, 'keystore must be an instance of jose.JWKS.KeyStore');
  assert(keystore.all().every(key => key.private), 'keystore must only contain private EC or RSA keys');
}

// if an OP doesnt support client_secret_basic but supports client_secret_post, use it instead
// this is in place to take care of most common pitfalls when first using discovered Issuers without
// the support for default values defined by Discovery 1.0
function checkBasicSupport(client, metadata, properties) {
  try {
    const supported = client.issuer.token_endpoint_auth_methods_supported;
    if (!supported.includes(properties.token_endpoint_auth_method)) {
      if (supported.includes('client_secret_post')) {
        properties.token_endpoint_auth_method = 'client_secret_post';
      }
    }
  } catch (err) {}
}

function handleCommonMistakes(client, metadata, properties) {
  if (!metadata.token_endpoint_auth_method) { // if no explicit value was provided
    checkBasicSupport(client, metadata, properties);
  }

  // :fp: c'mon people... RTFM
  if (metadata.redirect_uri) {
    assert(!metadata.redirect_uris, 'provide a redirect_uri or redirect_uris, not both');
    properties.redirect_uris = [metadata.redirect_uri];
    delete properties.redirect_uri;
  }

  if (metadata.response_type) {
    assert(!metadata.response_types, 'provide a response_type or response_types, not both');
    properties.response_types = [metadata.response_type];
    delete properties.response_type;
  }
}

function getDefaultsForEndpoint(endpoint, issuer, properties) {
  if (!issuer[`${endpoint}_endpoint`]) return;

  const tokenEndpointAuthMethod = properties.token_endpoint_auth_method;
  const tokenEndpointAuthSigningAlg = properties.token_endpoint_auth_signing_alg;

  const eam = `${endpoint}_endpoint_auth_method`;
  const easa = `${endpoint}_endpoint_auth_signing_alg`;

  if (properties[eam] === undefined && properties[easa] === undefined) {
    if (tokenEndpointAuthMethod !== undefined) {
      properties[eam] = tokenEndpointAuthMethod;
    }
    if (tokenEndpointAuthSigningAlg !== undefined) {
      properties[easa] = tokenEndpointAuthSigningAlg;
    }
  }
}

function assertSigningAlgValuesSupport(endpoint, issuer, properties) {
  if (!issuer[`${endpoint}_endpoint`]) return;

  const eam = `${endpoint}_endpoint_auth_method`;
  const easa = `${endpoint}_endpoint_auth_signing_alg`;
  const easavs = `${endpoint}_endpoint_auth_signing_alg_values_supported`;

  if (properties[eam] && properties[eam].endsWith('_jwt') && !properties[easa]) {
    assert(issuer[easavs], `${easavs} must be configured on the issuer if ${easa} is not defined on a client`);
  }
}

function assertIssuerConfiguration(issuer, endpoint) {
  assert(issuer[endpoint], `${endpoint} must be configured on the issuer`);
}

class Client {
  /**
   * @name constructor
   * @api public
   */
  constructor(metadata = {}, keystore) {
    const properties = Object.assign({}, CLIENT_DEFAULTS, metadata);

    handleCommonMistakes(this, metadata, properties);

    assertSigningAlgValuesSupport('token', this.issuer, properties);

    ['introspection', 'revocation'].forEach((endpoint) => {
      getDefaultsForEndpoint(endpoint, this.issuer, properties);
      assertSigningAlgValuesSupport(endpoint, this.issuer, properties);
    });

    Object.entries(properties).forEach(([key, value]) => {
      instance(this).get('metadata').set(key, value);
      if (!this[key]) {
        Object.defineProperty(this, key, {
          get() { return instance(this).get('metadata').get(key); },
        });
      }
    });

    if (keystore !== undefined) {
      checkStore.call(this, keystore);
      instance(this).set('keystore', keystore);
    }

    this.CLOCK_TOLERANCE = 0;
  }

  /**
   * @name authorizationUrl
   * @api public
   */
  authorizationUrl(params = {}) {
    assertIssuerConfiguration(this.issuer, 'authorization_endpoint');
    const target = url.parse(this.issuer.authorization_endpoint, true);
    target.search = null;
    Object.assign(target.query, authorizationParams.call(this, params));
    return url.format(target);
  }

  /**
   * @name authorizationPost
   * @api public
   */
  authorizationPost(params = {}) {
    const inputs = authorizationParams.call(this, params);
    const formInputs = Object.keys(inputs)
      .map(name => `<input type="hidden" name="${name}" value="${inputs[name]}"/>`).join('\n');

    return `<!DOCTYPE html>
<head>
  <title>Requesting Authorization</title>
</head>
<body onload="javascript:document.forms[0].submit()">
  <form method="post" action="${this.issuer.authorization_endpoint}">
    ${formInputs}
  </form>
</body>
</html>`;
  }

  /**
   * @name endSessionUrl
   * @api public
   */
  endSessionUrl(params = {}) {
    assertIssuerConfiguration(this.issuer, 'end_session_endpoint');

    const {
      0: postLogout,
      length,
    } = this.post_logout_redirect_uris || [];

    const {
      post_logout_redirect_uri = length === 1 ? postLogout : undefined,
    } = params;

    let hint = params.id_token_hint;

    if (hint instanceof TokenSet) {
      assert(hint.id_token, 'id_token not present in TokenSet');
      hint = hint.id_token;
    }

    const target = url.parse(this.issuer.end_session_endpoint, true);
    target.search = null;
    target.query = Object.assign(params, target.query, {
      post_logout_redirect_uri,
      id_token_hint: hint,
    });

    Object.entries(target.query).forEach(([key, value]) => {
      if (value === null || value === undefined) {
        delete target.query[key];
      }
    });

    return url.format(target);
  }

  /**
   * @name callbackParams
   * @api public
   */
  callbackParams(input) { // eslint-disable-line class-methods-use-this
    const isIncomingMessage = input instanceof stdhttp.IncomingMessage
      || (input && input.method && input.url);
    const isString = typeof input === 'string';

    assert(
      isString || isIncomingMessage,
      '#callbackParams only accepts string urls, http.IncomingMessage or a lookalike',
    );

    if (isIncomingMessage) {
      switch (input.method) {
        case 'GET':
          return pickCb(url.parse(input.url, true).query);
        case 'POST':
          assert(input.body, 'incoming message body missing, include a body parser prior to this call');
          switch (typeof input.body) {
            case 'object':
            case 'string':
              if (Buffer.isBuffer(input.body)) {
                return pickCb(querystring.parse(input.body.toString('utf-8')));
              }
              if (typeof input.body === 'string') {
                return pickCb(querystring.parse(input.body));
              }

              return pickCb(input.body);
            default:
              throw new Error('invalid IncomingMessage body object');
          }
        default:
          throw new Error('invalid IncomingMessage method');
      }
    } else {
      return pickCb(url.parse(input, true).query);
    }
  }

  /**
   * @name authorizationCallback
   * @api public
   */
  async authorizationCallback(
    redirectUri,
    parameters,
    checks = {},
  ) {
    const params = pickCb(parameters);

    if (this.default_max_age && !checks.max_age) checks.max_age = this.default_max_age;

    if (!params.state && checks.state) {
      throw new Error('state missing from the response');
    }

    if (params.state && !checks.state) {
      throw new Error('checks.state argument is missing');
    }

    if (checks.state !== params.state) {
      throw new Error('state mismatch');
    }

    if (params.error) {
      throw new OpenIdConnectError(params);
    }

    const RESPONSE_TYPE_REQUIRED_PARAMS = {
      code: ['code'],
      id_token: ['id_token'],
      token: ['access_token', 'token_type'],
    };

    if (checks.response_type) {
      for (const type of checks.response_type.split(' ')) { // eslint-disable-line no-restricted-syntax
        if (type === 'none') {
          if (params.code || params.id_token || params.access_token) {
            throw new Error('unexpected params encountered for "none" response');
          }
        } else {
          for (const param of RESPONSE_TYPE_REQUIRED_PARAMS[type]) { // eslint-disable-line no-restricted-syntax, max-len
            if (!params[param]) {
              throw new Error(`${param} missing from response`);
            }
          }
        }
      }
    }

    if (params.id_token) {
      const tokenset = new TokenSet(params);
      await this.decryptIdToken(tokenset);
      await this.validateIdToken(tokenset, checks.nonce, 'authorization', checks.max_age, checks.state);

      if (!params.code) {
        return tokenset;
      }
    }

    if (params.code) {
      const tokenset = await this.grant({
        grant_type: 'authorization_code',
        code: params.code,
        redirect_uri: redirectUri,
        code_verifier: checks.code_verifier,
      });

      await this.decryptIdToken(tokenset);
      await this.validateIdToken(tokenset, checks.nonce, 'token', checks.max_age);

      if (params.session_state) {
        tokenset.session_state = params.session_state;
      }

      return tokenset;
    }

    return new TokenSet(params);
  }

  /**
   * @name oauthCallback
   * @api public
   */
  async oauthCallback(redirectUri, parameters, checks = {}) {
    const params = pickCb(parameters);

    if (!params.state && checks.state) {
      throw new Error('state missing from the response');
    }

    if (params.state && !checks.state) {
      throw new Error('checks.state argument is missing');
    }

    if (checks.state !== params.state) {
      throw new Error('state mismatch');
    }

    if (params.error) {
      throw new OpenIdConnectError(params);
    }

    const RESPONSE_TYPE_REQUIRED_PARAMS = {
      code: ['code'],
      token: ['access_token', 'token_type'],
    };

    if (checks.response_type) {
      for (const type of checks.response_type.split(' ')) { // eslint-disable-line no-restricted-syntax
        if (type === 'none') {
          if (params.code || params.id_token || params.access_token) {
            throw new Error('unexpected params encountered for "none" response');
          }
        }

        if (RESPONSE_TYPE_REQUIRED_PARAMS[type]) {
          for (const param of RESPONSE_TYPE_REQUIRED_PARAMS[type]) { // eslint-disable-line no-restricted-syntax, max-len
            if (!params[param]) {
              throw new Error(`${param} missing from response`);
            }
          }
        }
      }
    }

    if (params.code) {
      return this.grant({
        grant_type: 'authorization_code',
        code: params.code,
        redirect_uri: redirectUri,
        code_verifier: checks.code_verifier,
      });
    }

    return new TokenSet(params);
  }

  /**
   * @name decryptIdToken
   * @api private
   */
  async decryptIdToken(token, use) {
    if (!use) use = 'id_token'; // eslint-disable-line no-param-reassign

    if (!this[`${use}_encrypted_response_alg`]) {
      return token;
    }

    let idToken = token;

    if (idToken instanceof TokenSet) {
      assert(idToken.id_token, 'id_token not present in TokenSet');
      idToken = idToken.id_token;
    }

    const expectedAlg = this[`${use}_encrypted_response_alg`];
    const expectedEnc = this[`${use}_encrypted_response_enc`];

    const header = JSON.parse(base64url.decode(idToken.split('.')[0]));

    assert.strictEqual(header.alg, expectedAlg, 'unexpected alg received');
    assert.strictEqual(header.enc, expectedEnc, 'unexpected enc received');

    let keyOrStore;

    if (expectedAlg.match(/^(RSA|ECDH)/)) {
      keyOrStore = instance(this).get('keystore');
    } else {
      keyOrStore = await this.joseSecret(expectedAlg);
    }

    const payload = jose.JWE.decrypt(idToken, keyOrStore);
    const result = payload.toString('utf8');

    if (token instanceof TokenSet) {
      token.id_token = result;
      return token;
    }

    return result;
  }

  /**
   * @name validateIdToken
   * @api private
   */
  async validateIdToken(tokenSet, nonce, returnedBy, maxAge, state) {
    let idToken = tokenSet;

    const expectedAlg = returnedBy === 'userinfo' ? this.userinfo_signed_response_alg : this.id_token_signed_response_alg;

    const isTokenSet = idToken instanceof TokenSet;

    if (isTokenSet) {
      assert(idToken.id_token, 'id_token not present in TokenSet');
      idToken = idToken.id_token;
    }

    idToken = String(idToken);

    const timestamp = now();
    const parts = idToken.split('.');
    const header = JSON.parse(base64url.decode(parts[0]));
    const payload = JSON.parse(base64url.decode(parts[1]));

    assert.strictEqual(header.alg, expectedAlg, 'unexpected algorithm received');

    if (returnedBy !== 'userinfo') {
      ['iss', 'sub', 'aud', 'exp', 'iat'].forEach(verifyPresence.bind(payload));
    }

    if (payload.iss !== undefined) {
      assert.strictEqual(payload.iss, this.issuer.issuer, 'unexpected iss value');
    }

    if (payload.iat !== undefined) {
      assert.strictEqual(typeof payload.iat, 'number', 'iat is not a number');
      assert(payload.iat <= timestamp + this.CLOCK_TOLERANCE, 'id_token issued in the future');
    }

    if (payload.nbf !== undefined) {
      assert.strictEqual(typeof payload.nbf, 'number', 'nbf is not a number');
      assert(payload.nbf <= timestamp + this.CLOCK_TOLERANCE, 'id_token not active yet');
    }

    if (maxAge || (maxAge !== null && this.require_auth_time)) {
      assert(payload.auth_time, 'missing required JWT property auth_time');
      assert.strictEqual(typeof payload.auth_time, 'number', 'auth_time is not a number');
    }

    if (maxAge) {
      assert(payload.auth_time + maxAge >= timestamp - this.CLOCK_TOLERANCE, 'too much time has elapsed since the last End-User authentication');
    }

    if (nonce !== null && (payload.nonce || nonce !== undefined)) {
      assert.strictEqual(payload.nonce, nonce, 'nonce mismatch');
    }

    if (payload.exp !== undefined) {
      assert.strictEqual(typeof payload.exp, 'number', 'exp is not a number');
      assert(timestamp - this.CLOCK_TOLERANCE < payload.exp, 'id_token expired');
    }

    if (payload.aud !== undefined) {
      if (!Array.isArray(payload.aud)) {
        payload.aud = [payload.aud];
      } else if (payload.aud.length > 1 && !payload.azp) {
        throw new Error('missing required JWT property azp');
      }
    }

    if (payload.azp !== undefined) {
      assert.strictEqual(payload.azp, this.client_id, 'azp must be the client_id');
    }

    if (payload.aud !== undefined) {
      assert(payload.aud.includes(this.client_id), 'aud is missing the client_id');
    }

    if (returnedBy === 'authorization') {
      assert(payload.at_hash || !tokenSet.access_token, 'missing required property at_hash');
      assert(payload.c_hash || !tokenSet.code, 'missing required property c_hash');

      if (payload.s_hash) {
        assert(state, 'cannot verify s_hash, state not provided');
        assert(tokenHash(payload.s_hash, state, header.alg), 's_hash mismatch');
      }
    }

    if (tokenSet.access_token && payload.at_hash !== undefined) {
      assert(tokenHash(payload.at_hash, tokenSet.access_token, header.alg), 'at_hash mismatch');
    }

    if (tokenSet.code && payload.c_hash !== undefined) {
      assert(tokenHash(payload.c_hash, tokenSet.code, header.alg), 'c_hash mismatch');
    }

    if (header.alg === 'none') {
      return tokenSet;
    }

    let key;

    if (header.alg.startsWith('HS')) {
      key = await this.joseSecret();
    } else {
      key = await this.issuer.key(header);
    }

    try {
      jose.JWS.verify(idToken, key);
    } catch (err) {
      throw new Error('invalid signature');
    }

    return tokenSet;
  }

  /**
   * @name refresh
   * @api public
   */
  async refresh(refreshToken) {
    let token = refreshToken;

    if (token instanceof TokenSet) {
      if (!token.refresh_token) {
        throw new Error('refresh_token not present in TokenSet');
      }
      token = token.refresh_token;
    }

    const tokenset = await this.grant({
      grant_type: 'refresh_token',
      refresh_token: String(token),
    });

    if (tokenset.id_token) {
      await this.decryptIdToken(tokenset);
      await this.validateIdToken(tokenset, null, 'token', null);
    }

    return tokenset;
  }

  /**
   * @name userinfo
   * @api public
   */
  async userinfo(accessToken, options) {
    assertIssuerConfiguration(this.issuer, 'userinfo_endpoint');
    let token = accessToken;
    const opts = merge({
      verb: 'get',
      via: 'header',
    }, options);

    if (token instanceof TokenSet) {
      if (!token.access_token) {
        throw new Error('access_token not present in TokenSet');
      }
      token = token.access_token;
    }

    const verb = String(opts.verb).toLowerCase();
    let httpOptions;

    switch (opts.via) {
      case 'query':
        assert.strictEqual(verb, 'get', 'providers should only parse query strings for GET requests');
        httpOptions = { query: { access_token: token } };
        break;
      case 'body':
        assert.strictEqual(verb, 'post', 'can only send body on POST');
        httpOptions = { form: true, body: { access_token: token } };
        break;
      default:
        httpOptions = { headers: { Authorization: bearer(token) } };
    }

    if (opts.params) {
      if (verb === 'post') {
        defaultsDeep(httpOptions, { body: opts.params });
      } else {
        defaultsDeep(httpOptions, { query: opts.params });
      }
    }

    const { issuer } = this;
    let response;
    try {
      response = await this.httpClient[verb](
        issuer.userinfo_endpoint,
        issuer.httpOptions(httpOptions),
      );
    } catch (err) {
      bearerErrorHandler.call(this, err);
    }

    processResponse(response, { parse: false });

    let parsed;
    if (JWT_CONTENT.test(response.headers['content-type'])) {
      const jwt = await this.decryptIdToken(response.body, 'userinfo');
      if (!this.userinfo_signed_response_alg) {
        parsed = JSON.parse(jwt);
      } else {
        await this.validateIdToken(jwt, null, 'userinfo', null);
        parsed = JSON.parse(base64url.decode(jwt.split('.')[1]));
      }
    } else {
      parsed = JSON.parse(response.body);
    }

    if (accessToken.id_token) {
      assert.strictEqual(parsed.sub, getSub(accessToken.id_token), 'userinfo sub mismatch');
    }

    return parsed;
  }

  /**
   * @name derivedKey
   * @api private
   */
  async derivedKey(len) {
    const cacheKey = `${len}_key`;
    if (instance(this).has(cacheKey)) {
      return instance(this).get(cacheKey);
    }

    const derivedBuffer = crypto.createHash('sha256')
      .update(this.client_secret)
      .digest()
      .slice(0, len / 8);

    const key = jose.JWK.importKey({ k: base64url.encode(derivedBuffer), kty: 'oct' });
    instance(this).set(cacheKey, key);

    return key;
  }

  /**
   * @name joseSecret
   * @api private
   */
  async joseSecret(alg) {
    if (String(alg).match(/^A(\d{3})(?:GCM)?KW$/)) {
      return this.derivedKey(parseInt(RegExp.$1, 10));
    }

    if (instance(this).has('jose_secret')) {
      return instance(this).get('jose_secret');
    }

    const key = jose.JWK.importKey({ k: base64url.encode(this.client_secret), kty: 'oct' });
    instance(this).set('jose_secret', key);

    return key;
  }

  /**
   * @name grant
   * @api public
   */
  async grant(body) {
    assertIssuerConfiguration(this.issuer, 'token_endpoint');
    const response = await this.authenticatedPost('token', { body: omitBy(body, arg => typeof arg === 'undefined') });

    return new TokenSet(processResponse(response));
  }

  /**
   * @name revoke
   * @api public
   */
  async revoke(token, hint) {
    assertIssuerConfiguration(this.issuer, 'revocation_endpoint');
    assert(!hint || typeof hint === 'string', 'hint must be a string');

    const body = { token };

    if (hint) {
      body.token_type_hint = hint;
    }

    const response = await this.authenticatedPost('revocation', { body });
    processResponse(response, { body: false, parse: false });
  }

  /**
   * @name introspect
   * @api public
   */
  async introspect(token, hint) {
    assertIssuerConfiguration(this.issuer, 'introspection_endpoint');
    assert(!hint || typeof hint === 'string', 'hint must be a string');

    const body = { token };
    if (hint) {
      body.token_type_hint = hint;
    }

    const response = await this.authenticatedPost('introspection', { body });

    return processResponse(response);
  }

  /**
   * @name fetchDistributedClaims
   * @api public
   */
  async fetchDistributedClaims(claims, tokens = {}) {
    if (!isPlainObject(claims)) throw new Error('claims argument must be a plain object');
    if (!isPlainObject(claims._claim_sources)) return claims;
    if (!isPlainObject(claims._claim_names)) return claims;

    const distributedSources = Object.entries(claims._claim_sources)
      .filter(([, value]) => value && value.endpoint);

    await Promise.all(distributedSources.map(async ([sourceName, def]) => {
      try {
        const opts = {
          headers: { Authorization: bearer(def.access_token || tokens[sourceName]) },
        };

        const response = await this.httpClient.get(
          def.endpoint,
          this.issuer.httpOptions(opts),
        ).catch(bearerErrorHandler.bind(this));

        const decoded = await claimJWT.call(this, response.body);
        delete claims._claim_sources[sourceName];
        Object.entries(claims._claim_names).forEach(assignClaim(claims, decoded, sourceName));
      } catch (err) {
        err.src = sourceName;
        throw err;
      }
    }));

    cleanUpClaims(claims);
    return claims;
  }

  /**
   * @name unpackAggregatedClaims
   * @api public
   */
  async unpackAggregatedClaims(claims) {
    if (!isPlainObject(claims)) throw new Error('claims argument must be a plain object');
    if (!isPlainObject(claims._claim_sources)) return claims;
    if (!isPlainObject(claims._claim_names)) return claims;

    const aggregatedSources = Object.entries(claims._claim_sources)
      .filter(([, value]) => value && value.JWT);

    await Promise.all(aggregatedSources.map(async ([sourceName, def]) => {
      try {
        const decoded = await claimJWT.call(this, def.JWT);
        delete claims._claim_sources[sourceName];
        Object.entries(claims._claim_names).forEach(assignClaim(claims, decoded, sourceName));
      } catch (err) {
        err.src = sourceName;
        throw err;
      }
    }));

    cleanUpClaims(claims);
    return claims;
  }

  /**
   * @name authenticatedPost
   * @api private
   */
  async authenticatedPost(endpoint, httpOptions) {
    const auth = await this.authFor(endpoint);
    const opts = this.issuer.httpOptions(merge(httpOptions, auth, { form: true }));

    return this.httpClient.post(
      this.issuer[`${endpoint}_endpoint`],
      opts,
    ).catch(errorHandler.bind(this));
  }

  /**
   * @name clientAssertion
   * @api private
   */
  async clientAssertion(endpoint = 'token', payload) {
    let alg = this[`${endpoint}_endpoint_auth_signing_alg`];
    if (!alg) {
      assertIssuerConfiguration(this.issuer, `${endpoint}_endpoint_auth_signing_alg_values_supported`);
    }

    switch (this[`${endpoint}_endpoint_auth_method`]) {
      case 'client_secret_jwt': {
        const key = await this.joseSecret();

        if (!alg) {
          const supported = this.issuer[`${endpoint}_endpoint_auth_signing_alg_values_supported`];
          alg = Array.isArray(supported) && supported.find(signAlg => key.algorithms('sign').has(signAlg));
        }

        return jose.JWS.sign(payload, key, {
          alg,
          typ: 'JWT',
        });
      }
      case 'private_key_jwt': {
        if (!alg) {
          const algs = new Set();

          instance(this).get('keystore').all().forEach((key) => {
            key.algorithms('sign').forEach(Set.prototype.add.bind(algs));
          });

          const supported = this.issuer[`${endpoint}_endpoint_auth_signing_alg_values_supported`];
          alg = Array.isArray(supported) && supported.find(signAlg => algs.has(signAlg));
        }

        const key = instance(this).get('keystore').get({ alg, use: 'sig' });
        assert(key, 'no valid key found');
        return jose.JWS.sign(payload, key, {
          alg,
          typ: 'JWT',
          kid: key.kid,
        });
      }
      /* istanbul ignore next */
      default:
        throw new Error('createSign only works for _jwt token auth methods');
    }
  }

  /**
   * @name authFor
   * @api private
   */
  async authFor(endpoint = 'token') {
    const authMethod = this[`${endpoint}_endpoint_auth_method`];
    switch (authMethod) {
      case 'none':
        return {
          body: {
            client_id: this.client_id,
          },
        };
      case 'client_secret_post':
        return {
          body: {
            client_id: this.client_id,
            client_secret: this.client_secret,
          },
        };
      case 'private_key_jwt':
      case 'client_secret_jwt': {
        const timestamp = now();
        const assertion = await this.clientAssertion(endpoint, {
          iat: timestamp,
          exp: timestamp + 60,
          jti: random(),
          iss: this.client_id,
          sub: this.client_id,
          aud: this.issuer[`${endpoint}_endpoint`],
        });

        return {
          body: {
            client_assertion: assertion,
            client_assertion_type: 'urn:ietf:params:oauth:client-assertion-type:jwt-bearer',
          },
        };
      }
      default: {
        const encoded = `${formUrlEncode(this.client_id)}:${formUrlEncode(this.client_secret)}`;
        const value = Buffer.from(encoded).toString('base64');
        return { headers: { Authorization: `Basic ${value}` } };
      }
    }
  }

  /**
   * @name register
   * @api public
   */
  static async register(properties, { initialAccessToken, keystore } = {}) {
    assertIssuerConfiguration(this.issuer, 'registration_endpoint');

    if (keystore !== undefined && !(properties.jwks || properties.jwks_uri)) {
      checkStore.call(this, keystore);
      properties.jwks = keystore.toJWKS();
    }

    const headers = { 'Content-Type': 'application/json' };

    if (initialAccessToken) {
      headers.Authorization = bearer(initialAccessToken);
    }

    let response;
    try {
      response = await this.httpClient.post(
        this.issuer.registration_endpoint,
        this.issuer.httpOptions({ headers, body: JSON.stringify(properties) }),
      );
    } catch (err) {
      bearerErrorHandler.call(this, err);
    }

    return new this(processResponse(response, { statusCode: 201 }), keystore);
  }

  /**
   * @name metadata
   * @api public
   */
  get metadata() {
    const copy = {};
    instance(this).get('metadata').forEach((value, key) => {
      copy[key] = value;
    });
    return copy;
  }

  /**
   * @name fromUri
   * @api public
   */
  static async fromUri(registrationClientUri, registrationAccessToken, keystore) {
    let response;

    try {
      response = await this.httpClient.get(
        registrationClientUri,
        this.issuer.httpOptions({ headers: { Authorization: bearer(registrationAccessToken) } }),
      );
    } catch (err) {
      bearerErrorHandler.call(this, err);
    }

    return new this(processResponse(response), keystore);
  }

  /**
   * @name requestObject
   * @api public
   */
  async requestObject(request = {}, algorithms = {}) {
    assert(isPlainObject(request), 'pass a plain object as the first argument');

    defaults(algorithms, {
      sign: this.request_object_signing_alg,
      encrypt: {
        alg: this.request_object_encryption_alg,
        enc: this.request_object_encryption_enc,
      },
    }, {
      sign: 'none',
    });

    let signed;
    let key;

    const alg = algorithms.sign;
    const header = { alg, typ: 'JWT' };
    const payload = JSON.stringify(defaults({}, request, {
      iss: this.client_id,
      aud: this.issuer.issuer,
      client_id: this.client_id,
    }));

    if (alg === 'none') {
      signed = [
        base64url.encode(JSON.stringify(header)),
        base64url.encode(payload),
        '',
      ].join('.');
    } else {
      const symmetrical = alg.startsWith('HS');
      if (symmetrical) {
        key = await this.joseSecret();
      } else {
        const keystore = instance(this).get('keystore');

        assert(keystore, `no keystore present for client, cannot sign using ${alg}`);
        key = keystore.get({ alg, use: 'sig' });
        assert(key, `no key to sign with found for ${alg}`);
      }

      signed = jose.JWS.sign(payload, key, {
        ...header,
        kid: symmetrical ? undefined : key.kid,
      });
    }

    if (!algorithms.encrypt.alg) {
      return signed;
    }

    const fields = { alg: algorithms.encrypt.alg, enc: algorithms.encrypt.enc, cty: 'JWT' };

    if (fields.alg.match(/^(RSA|ECDH)/)) {
      key = await this.issuer.key({
        alg: fields.alg,
        enc: fields.enc,
        use: 'enc',
      }, true);
    } else {
      key = await this.joseSecret(fields.alg);
    }

    return jose.JWE.encrypt(signed, key, {
      ...fields,
      kid: key.kty === 'oct' ? undefined : key.kid,
    });
  }

  resolveResponseType() {
    const { length, 0: value } = this.response_types;

    if (length === 1) {
      return value;
    }

    return undefined;
  }

  resolvedRedirectUri() {
    const { length, 0: value } = this.redirect_uris || [];

    if (length === 1) {
      return value;
    }

    return undefined;
  }

  get httpClient() {
    return this.issuer.httpClient;
  }

  static get httpClient() {
    return this.issuer.httpClient;
  }

  /* istanbul ignore next */
  [util.inspect.custom]() {
    return util.format('Client <%s>', this.client_id);
  }
}

module.exports = Client;
