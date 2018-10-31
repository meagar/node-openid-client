const assert = require('assert');
const util = require('util');
const url = require('url');

const jose = require('@panva/jose');
const { clone, merge } = require('lodash');
const pAny = require('p-any');
const LRU = require('lru-cache');

const http = require('./http');
const errorHandler = require('./helpers/error_handler')();
const BaseClient = require('./client');
const registry = require('./issuer_registry');
const processResponse = require('./helpers/process_response');
const webfingerNormalize = require('./util/webfinger_normalize');
const instance = require('./helpers/weak_cache');
const {
  DEFAULT_HTTP_OPTIONS, ISSUER_DEFAULTS, OIDC_DISCOVERY, OAUTH2_DISCOVERY, WEBFINGER, REL,
} = require('./helpers/consts');


let defaultHttpOptions = clone(DEFAULT_HTTP_OPTIONS);
let httpClient;

class Issuer {
  /**
   * @name constructor
   * @api public
   */
  constructor(meta = {}) {
    ['introspection', 'revocation'].forEach((endpoint) => {
      // if intro/revocation endpoint auth specific meta is missing use the token ones if they
      // are defined
      if (
        meta[`${endpoint}_endpoint`]
        && meta[`${endpoint}_endpoint_auth_methods_supported`] === undefined
        && meta[`${endpoint}_endpoint_auth_signing_alg_values_supported`] === undefined
      ) {
        if (meta.token_endpoint_auth_methods_supported) {
          meta[`${endpoint}_endpoint_auth_methods_supported`] = meta.token_endpoint_auth_methods_supported;
        }
        if (meta.token_endpoint_auth_signing_alg_values_supported) {
          meta[`${endpoint}_endpoint_auth_signing_alg_values_supported`] = meta.token_endpoint_auth_signing_alg_values_supported;
        }
      }
    });

    Object.entries(meta).forEach(([key, value]) => {
      instance(this).get('metadata').set(key, value);
      if (!this[key]) {
        Object.defineProperty(this, key, {
          get() { return instance(this).get('metadata').get(key); },
        });
      }
    });

    instance(this).set('cache', new LRU({ max: 100 }));

    registry.set(this.issuer, this);

    const self = this;

    Object.defineProperty(this, 'Client', {
      value: class Client extends BaseClient {
        static get issuer() {
          return self;
        }

        get issuer() {
          return this.constructor.issuer;
        }
      },
    });
  }

  /**
   * @name keystore
   * @api public
   */
  async keystore(reload = false) {
    if (!this.jwks_uri) throw new Error('jwks_uri must be configured');

    const keystore = instance(this).get('keystore');
    const cache = instance(this).get('cache');

    if (reload || !keystore) {
      cache.reset();
      return this.httpClient.get(this.jwks_uri, this.httpOptions())
        .then(processResponse)
        .then(jwks => jose.JWKS.KeyStore.fromJWKS(jwks))
        .then((joseKeyStore) => {
          cache.set('throttle', true, 60 * 1000);
          instance(this).set('keystore', joseKeyStore);
          return joseKeyStore;
        })
        .catch(errorHandler.bind(this));
    }

    return keystore;
  }

  /**
   * @name key
   * @api public
   */
  async key(def, allowMulti = false) {
    const cache = instance(this).get('cache');

    // refresh keystore on every unknown key but also only upto once every minute
    const freshJwksUri = cache.get(def) || cache.get('throttle');

    return this.keystore(!freshJwksUri)
      .then(store => store.all(def))
      .then((keys) => {
        assert(keys.length, 'no valid key found');
        if (!allowMulti) {
          assert.strictEqual(keys.length, 1, 'multiple matching keys, kid must be provided');
          cache.set(def, true);
        }
        return keys[0];
      });
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
   * @name webfinger
   * @api public
   */
  static async webfinger(input) {
    const resource = webfingerNormalize(input);
    const { host } = url.parse(resource);
    const query = { resource, rel: REL };
    const opts = { query, followRedirect: true };
    const webfingerUrl = `https://${host}${WEBFINGER}`;

    return this.httpClient.get(webfingerUrl, this.httpOptions(opts))
      .then(processResponse)
      .then((body) => {
        const location = Array.isArray(body.links) && body.links.find(link => typeof link === 'object' && link.rel === REL && link.href);
        assert(location, 'no issuer found in webfinger');
        assert(typeof location.href === 'string' && location.href.startsWith('https://'), 'invalid issuer location');
        const expectedIssuer = location.href;
        if (registry.has(expectedIssuer)) return registry.get(expectedIssuer);

        return this.discover(expectedIssuer).then((issuer) => {
          try {
            assert.strictEqual(issuer.issuer, expectedIssuer, 'discovered issuer mismatch');
          } catch (err) {
            registry.delete(issuer.issuer);
            throw err;
          }
          return issuer;
        });
      });
  }

  /**
   * @name discover
   * @api public
   */
  static async discover(uri) {
    const parsed = url.parse(uri);

    if (parsed.pathname.includes('/.well-known/')) {
      return this.httpClient.get(uri, this.httpOptions())
        .then(processResponse)
        .then(body => new this(Object.assign({}, ISSUER_DEFAULTS, body)))
        .catch(errorHandler.bind(this));
    }

    const uris = [];
    if (parsed.pathname === '/') {
      uris.push(`${OAUTH2_DISCOVERY}`);
    } else {
      uris.push(`${OAUTH2_DISCOVERY}${parsed.pathname}`);
    }
    if (parsed.pathname.endsWith('/')) {
      uris.push(`${parsed.pathname}${OIDC_DISCOVERY.substring(1)}`);
    } else {
      uris.push(`${parsed.pathname}${OIDC_DISCOVERY}`);
    }

    return pAny(uris.map((pathname) => {
      const wellKnownUri = url.format(Object.assign({}, parsed, { pathname }));
      return this.httpClient.get(wellKnownUri, this.httpOptions())
        .then(processResponse)
        .then(body => new this(Object.assign({}, ISSUER_DEFAULTS, body)));
    }))
      .catch((err) => {
        if (err instanceof pAny.AggregateError) {
          for (const el of err) { // eslint-disable-line no-restricted-syntax
            if (el instanceof this.httpClient.HTTPError) throw el;
            if (el.message.startsWith('expected 200 OK, got ')) throw el;
            if (el.message === 'only valid absolute URLs can be requested') throw el;
            if (el instanceof SyntaxError) throw el;
          }
        }
        throw err;
      })
      .catch(errorHandler.bind(this));
  }

  static useGot() {
    this.httpClient = http.got();
  }

  static useRequest() {
    this.httpClient = http.request();
  }

  get httpClient() {
    return this.constructor.httpClient;
  }

  static get httpClient() {
    if (!httpClient) {
      this.useGot();
    }

    return httpClient;
  }

  static set httpClient(client) {
    assert.strictEqual(typeof client.get, 'function', 'client.get must be a function');
    assert.strictEqual(typeof client.post, 'function', 'client.post must be a function');
    assert(client.HTTPError, 'client.HTTPError must be a constructor');
    httpClient = client;
  }

  /**
   * @name httpOptions
   * @api public
   */
  httpOptions(...args) {
    return this.constructor.httpOptions(...args);
  }

  /**
   * @name httpOptions
   * @api public
   */
  static httpOptions(values) {
    return merge({}, this.defaultHttpOptions, values);
  }

  /**
   * @name defaultHttpOptions
   * @api public
   */
  static get defaultHttpOptions() {
    return defaultHttpOptions;
  }

  /**
   * @name defaultHttpOptions=
   * @api public
   */
  static set defaultHttpOptions(value) {
    defaultHttpOptions = merge({}, DEFAULT_HTTP_OPTIONS, value);
  }

  /* istanbul ignore next */
  [util.inspect.custom]() {
    return util.format('Issuer <%s>', this.issuer);
  }
}

module.exports = Issuer;
