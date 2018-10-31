/* eslint-disable global-require, import/no-dynamic-require */

const isAbsoluteUrl = require('../helpers/is_absolute_url');

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

const gotLibraryName = 'got';
module.exports = function gotWrapper() {
  // intended use of non-global & dynamic require
  // webpack will not include "got" in the bundle now
  const got = require(gotLibraryName);

  return {
    HTTPError: got.HTTPError,
    get(url, options) {
      isAbsoluteUrl(url);
      return got.get(url, options);
    },
    post(url, options) {
      isAbsoluteUrl(url);
      return got.post(url, options);
    },
  };
};
