// node --test tests/estimator.test.cjs — the browser estimator must match monitor/estimate.py.
const test = require("node:test");
const assert = require("node:assert");
const E = require("../static/estimator.js");

test("reference: 2^128 at 19.3e9 ops/s", () => {
  const one = E.estimate(E.workLog10("log2", "128"), 1, 19.3e9);
  assert.strictEqual(one.years, "5.59e+20");
  assert.strictEqual(one.gpuYears, "5.59e+20");
  const million = E.estimate(E.workLog10("log2", "2^128"), 1e6, E.parseNumber("19.3e9"));
  assert.strictEqual(million.years, "5.59e+14");
  assert.strictEqual(million.gpuYears, "5.59e+20");
  assert.strictEqual(million.seconds, "1.76e+22");
});

test("scientific input equals log2 input and never overflows", () => {
  const a = E.workLog10("log2", "128");
  const b = E.workLog10("sci", "3.402823669e38");
  assert.ok(Math.abs(a - b) < 1e-9);
  const huge = E.workLog10("sci", "1e1000"); // > Number.MAX_VALUE
  assert.strictEqual(huge, 1000);
  assert.strictEqual(E.estimate(huge, 1, 1).seconds, "1.00e+1000");
});

test("parsing and validation", () => {
  assert.strictEqual(E.parseNumber("1,000,000"), 1e6);
  assert.ok(Number.isNaN(E.parseNumber("1e")));
  assert.ok(Number.isNaN(E.parseNumber("<img>")));
  assert.throws(() => E.workLog10("log2", "-1"));
  assert.throws(() => E.workLog10("log2", "abc"));
  assert.throws(() => E.workLog10("sci", "0"));
  assert.throws(() => E.estimate(10, 0, 1));
  assert.throws(() => E.estimate(10, 1, -5));
  assert.strictEqual(E.sci(Math.log10(9.9996)), "1.00e+1");
});
