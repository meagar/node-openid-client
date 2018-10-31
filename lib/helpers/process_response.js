const assert = require('assert');
const { STATUS_CODES } = require('http');

function processResponse(response, { statusCode = 200, body = true, parse = true } = {}) {
  assert.strictEqual(
    response.statusCode,
    statusCode,
    `expected ${statusCode} ${STATUS_CODES[statusCode]}, got ${response.statusCode} ${STATUS_CODES[response.statusCode]} instead`,
  );

  if (body) {
    assert(
      response.body,
      `expected ${statusCode} ${STATUS_CODES[statusCode]} with body but no body was returned`,
    );
  }

  if (!parse) return undefined;

  return JSON.parse(response.body);
}


module.exports = processResponse;
