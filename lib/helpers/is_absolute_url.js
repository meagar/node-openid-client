const { parse } = require('url');

module.exports = (target) => {
  try {
    const { protocol } = parse(target);
    if (!protocol) {
      throw new Error();
    }
    return true;
  } catch (err) {
    throw new Error('only valid absolute URLs can be requested');
  }
};
