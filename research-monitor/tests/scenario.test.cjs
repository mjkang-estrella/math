// node --test tests/scenario.test.cjs — hardware choices, what-if multipliers and the baseline/current comparison.
const test = require("node:test");
const assert = require("node:assert");
const path = require("node:path");
const fs = require("node:fs");
const E = require("../static/estimator.js");
const CFG = JSON.parse(fs.readFileSync(path.join(__dirname, "..", "manifest.json"), "utf8")).estimator;

const yrs = (sel) => E.scenario(CFG, Object.assign({ gpus: 1, log2Work: 128 }, sel));

test("reference RTX 5090 rate is the measured default: 1 GPU and 1e6 GPUs", () => {
  const one = yrs({ hardware: "rtx5090", multiplier: 1 });
  assert.strictEqual(one.rate.basis, "measured");
  assert.strictEqual(one.result.years, "5.59e+20");
  const mil = yrs({ hardware: "rtx5090", multiplier: 1, gpus: 1e6 });
  assert.strictEqual(mil.result.years, "5.59e+14");
  assert.strictEqual(E.humanYears(mil.result.log10Years), "559 trillion years");
});

test("H200 and B200 have no benchmark: selecting them yields no number and no speedup", () => {
  for (const id of ["h200", "b200"]) {
    const hw = CFG.hardware.find((h) => h.id === id);
    assert.strictEqual(hw.benchmarked, false);
    assert.strictEqual(hw.ops_per_sec, null, id + " must not carry a fabricated rate");
    const s = yrs({ hardware: id, multiplier: null, gpus: 1e6 });
    assert.strictEqual(s.rate.known, false);
    assert.strictEqual(s.rate.basis, "unknown");
    assert.strictEqual(s.result, undefined);
  }
});

test("explicit what-if multipliers on unbenchmarked hardware are labelled assumed, never measured", () => {
  const same = yrs({ hardware: "h200", multiplier: 1, gpus: 1e6 });
  assert.strictEqual(same.rate.basis, "assumed");
  assert.strictEqual(same.result.years, "5.59e+14"); // 1x = reference rate, not a hidden speedup
  const x100 = yrs({ hardware: "b200", multiplier: 100, gpus: 1e6 });
  assert.strictEqual(x100.rate.basis, "assumed");
  assert.strictEqual(x100.result.years, "5.59e+12");
  assert.strictEqual(E.humanYears(x100.result.log10Years), "5.6 trillion years");
  // a multiplier above 1 on the measured GPU is also an assumption
  assert.strictEqual(yrs({ hardware: "rtx5090", multiplier: 10 }).rate.basis, "assumed");
  assert.throws(() => yrs({ hardware: "h200", multiplier: -1 }));
});

test("GPU count scales linearly: constants change, total GPU-years do not", () => {
  const a = yrs({ hardware: "rtx5090", multiplier: 1, gpus: 1 }).result;
  const b = yrs({ hardware: "rtx5090", multiplier: 1, gpus: 1e6 }).result;
  assert.ok(Math.abs(a.log10Years - b.log10Years - 6) < 1e-12);
  assert.strictEqual(a.gpuYears, b.gpuYears);
});

test("custom rate requires a positive measured value", () => {
  assert.strictEqual(yrs({ hardware: "custom", customRate: NaN }).rate.known, false);
  assert.strictEqual(yrs({ hardware: "custom", customRate: 0 }).rate.known, false);
  const c = yrs({ hardware: "custom", customRate: 19.3e9 });
  assert.strictEqual(c.rate.basis, "custom");
  assert.strictEqual(c.result.years, "5.59e+20");
  assert.strictEqual(yrs({ hardware: "nonexistent" }).rate.known, false);
});

test("baseline stays flat unless a reviewed comparable result exists", () => {
  assert.strictEqual(CFG.current_result, null, "live manifest must not claim an improvement");
  for (const status of ["reported_none", "reported_positive", "conflicting", "unknown"]) {
    const c = E.comparison(CFG, { status });
    assert.strictEqual(c.currentLog2, c.baselineLog2, status);
    assert.strictEqual(c.changed, false, status);
    assert.strictEqual(c.pendingClaim, status === "reported_positive" || status === "conflicting");
  }
  // keyword claim alone, or an unreviewed / wrong-unit entry, never moves the number
  for (const bad of [{ log2_work: 100, units: "group operations", source: "x" },
                     { log2_work: 100, units: "equality tests", reviewed: true, source: "x" },
                     { log2_work: 100, units: "group operations", reviewed: true }]) {
    const c = E.comparison(Object.assign({}, CFG, { current_result: bad }), { status: "reported_positive" });
    assert.strictEqual(c.changed, false);
  }
  const ok = E.comparison(Object.assign({}, CFG, { current_result: { log2_work: 100, units: "group operations", reviewed: true, source: "W999" } }), { status: "reported_positive" });
  assert.strictEqual(ok.changed, true);
  assert.strictEqual(ok.currentLog2, 100);
});

test("human-readable durations", () => {
  assert.strictEqual(E.humanYears(Math.log10(1.38e10)), "13.8 billion years");
  assert.strictEqual(E.humanYears(0), "1 year");
  assert.strictEqual(E.humanYears(Math.log10(2 / 365.25)), "2 days");
  assert.strictEqual(E.humanYears(50), "10^50 years");
});
