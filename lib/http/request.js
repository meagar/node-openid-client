/* eslint-disable global-require, import/no-dynamic-require */

const http = require('http');
const { promisify } = require('util');

const makeError = require('make-error');

const isAbsoluteUrl = require('../helpers/is_absolute_url');

function HTTPError(response) {
  const statusMessage = http.STATUS_CODES[response.statusCode];
  HTTPError.super.call(this, `Response code ${response.statusCode} (${statusMessage})`);

  Object.assign(
    this,
    {
      statusCode: response.statusCode,
      statusMessage,
      headers: response.headers,
      response,
    },
  );
}

makeError(HTTPError);

/*
 * url {String}
 * options {Object}
 * options.headers {Object}
 * options.body {String|Object}
 * options.form {Boolean}
 * options.query {Object}
 * options.timeout {Number}
 * options.retry {Number}
 * options.followRedirect {Boolean}
 */

const requestLibraryName = 'request';
module.exports = function requestWrapper() {
  // intended use of non-global & dynamic require
  // webpack will not include "request" in the bundle now
  const request = promisify(require(requestLibraryName));

  async function requestWrap(method, url, options) {
    isAbsoluteUrl(url);
    if (options.form) {
      options.form = options.body;
      options.body = undefined;
    }
    const response = await request({
      method,
      url,
      headers: options.headers,
      qs: options.query,
      body: options.body,
      form: options.form,
      followRedirect: options.followRedirect,
      timeout: options.timeout,
    });

    const { statusCode } = response;
    const limitStatusCode = options.followRedirect ? 299 : 399;

    if (statusCode !== 304 && (statusCode < 200 || statusCode > limitStatusCode)) {
      throw new HTTPError(response);
    }

    return response;
  }

  return {
    HTTPError,
    get(url, options) {
      return requestWrap('GET', url, options);
    },
    post(url, options) {
      return requestWrap('POST', url, options);
    },
  };
};
