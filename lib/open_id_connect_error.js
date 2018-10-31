/* eslint-disable camelcase */
const makeError = require('make-error');

function OpenIdConnectError({
  error_description,
  error,
  error_uri,
  session_state,
  state,
  scope,
}, response) {
  OpenIdConnectError.super.call(this, !error_description ? error : `${error} (${error_description})`);

  Object.assign(
    this,
    { error },
    (error_description && { error_description }),
    (error_uri && { error_uri }),
    (state && { state }),
    (scope && { scope }),
    (session_state && { session_state }),
  );

  Object.defineProperty(this, 'response', {
    value: response,
  });
}

makeError(OpenIdConnectError);

module.exports = OpenIdConnectError;
