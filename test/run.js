/* eslint-disable no-console */

const assert = require('assert');

const { all: clearRequireCache } = require('clear-module');
const Mocha = require('mocha');

let Issuer;

const implementations = {
  got: {
    label: 'https://github.com/sindresorhus/got',
  },
  request: {
    label: 'https://github.com/request/request',
    cmd() {
      Issuer.useRequest();
    },
  },
};

const FORMAT_REGEXP = /^--transport=(\w+)$/;
const transports = [];
process.argv.forEach((arg) => {
  if (FORMAT_REGEXP.exec(arg)) {
    assert(implementations[RegExp.$1]);
    transports.push(RegExp.$1);
  }
});

if (!transports.length) {
  transports.push('got');
  transports.push('request');
}
const passed = [];

const { utils: { lookupFiles } } = Mocha;
const files = lookupFiles('test/**/*.test.js', ['js'], true);
class SuiteFailedError extends Error {}

async function run() {
  clearRequireCache();
  await new Promise((resolve, reject) => {
    const mocha = new Mocha();
    mocha.files = files;

    if (process.env.CI) {
      mocha.retries(1); // retry flaky time comparison tests
      mocha.forbidOnly(); // force suite fail on encountered only test
      mocha.forbidPending(); // force suite fail on encountered skip test
    }

    ({ Issuer } = require('../lib')); // eslint-disable-line global-require
    if (this.cmd) this.cmd();

    console.log(`Running suite with ${this.label} http client implementation`);
    mocha.run((failures) => {
      if (!failures) {
        passed.push(`Suite passed with ${this.label} http client implementation`);
        resolve();
      } else {
        reject(new SuiteFailedError(`Suite failed with ${this.label} http client implementation`));
      }
    });
  });
}

(async () => {
  for (const transport of transports) { // eslint-disable-line no-restricted-syntax
    await run.call(implementations[transport]); // eslint-disable-line no-await-in-loop
  }
  passed.forEach(pass => console.log('\x1b[32m%s\x1b[0m', pass));
})()
  .catch((error) => {
    passed.forEach(pass => console.log('\x1b[32m%s\x1b[0m', pass));
    if (error instanceof SuiteFailedError) {
      console.log('\x1b[31m%s\x1b[0m', error.message);
    } else {
      console.error(error);
    }
    process.exitCode = 1;
  });
