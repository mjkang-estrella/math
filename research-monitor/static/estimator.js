/* Rough runtime arithmetic in log10 space (mirrors monitor/estimate.py).
 * time = work / (gpus * opsPerSecPerGpu), perfect linear scaling assumed.
 * Works as a browser global (window.Estimator) and a CommonJS module for tests. */
(function (root) {
  "use strict";
  var SECONDS_PER_DAY = 86400;
  var SECONDS_PER_YEAR = 365.25 * SECONDS_PER_DAY;
  var LOG10_2 = Math.log10(2);
  var MAX_LOG2_WORK = 4096;

  function fail(msg) { var e = new Error(msg); e.name = "EstimateError"; throw e; }

  /** Parse a number written as plain decimal or scientific notation ("19.3e9", "1,000,000"). */
  function parseNumber(text) {
    if (typeof text === "number") return text;
    var s = String(text == null ? "" : text).trim().replace(/[,_\s]/g, "");
    if (!/^[+]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/.test(s)) return NaN;
    return Number(s);
  }

  /** Work as log10(ops). mode "log2": text is the exponent (e.g. "128" or "2^128");
   *  mode "sci": text is a count such as "3.4e38". Huge sci values are parsed via
   *  mantissa/exponent so they never overflow to Infinity. */
  function workLog10(mode, text) {
    var s = String(text == null ? "" : text).trim();
    if (mode === "log2") {
      s = s.replace(/^2\s*\^\s*/, "");
      var x = parseNumber(s);
      if (!isFinite(x) || x < 0 || x > MAX_LOG2_WORK) fail("log2 work must be a number in [0, " + MAX_LOG2_WORK + "]");
      return x * LOG10_2;
    }
    var m = /^\s*\+?(\d+\.?\d*|\.\d+)\s*(?:[eE]\s*([+-]?\d+)|[x×*]\s*10\s*\^\s*([+-]?\d+))?\s*$/.exec(s.replace(/[,_]/g, ""));
    if (!m) fail("work must look like 3.4e38");
    var mant = Number(m[1]);
    var exp = Number(m[2] || m[3] || 0);
    if (!(mant > 0)) fail("work must be positive");
    var l = Math.log10(mant) + exp;
    if (!isFinite(l) || l < 0 || l > MAX_LOG2_WORK * LOG10_2) fail("work must be between 1 and 2^" + MAX_LOG2_WORK);
    return l;
  }

  function sci(log10v, digits) {
    digits = digits || 3;
    if (!isFinite(log10v)) return "—";
    var exp = Math.floor(log10v);
    var mant = Math.pow(10, log10v - exp);
    if (Number(mant.toFixed(digits - 1)) >= 10) { mant /= 10; exp += 1; }
    return mant.toFixed(digits - 1) + "e" + (exp >= 0 ? "+" : "") + exp;
  }

  function estimate(log10Ops, gpus, rate) {
    if (!(isFinite(gpus) && gpus > 0)) fail("GPU count must be a positive number");
    if (!(isFinite(rate) && rate > 0)) fail("operations/second/GPU must be a positive number");
    var log10Seconds = log10Ops - Math.log10(gpus) - Math.log10(rate);
    var log10Years = log10Seconds - Math.log10(SECONDS_PER_YEAR);
    return {
      log10Ops: log10Ops,
      log2Ops: log10Ops / LOG10_2,
      log10Seconds: log10Seconds,
      log10Days: log10Seconds - Math.log10(SECONDS_PER_DAY),
      log10Years: log10Years,
      log10GpuYears: log10Years + Math.log10(gpus),
      seconds: sci(log10Seconds),
      days: sci(log10Seconds - Math.log10(SECONDS_PER_DAY)),
      years: sci(log10Years),
      gpuYears: sci(log10Years + Math.log10(gpus))
    };
  }

  // ---------- Scenarios (hardware choice never invents a benchmark) ----------
  function findHw(cfg, id) {
    var list = (cfg && cfg.hardware) || [];
    for (var i = 0; i < list.length; i++) if (list[i].id === id) return list[i];
    return null;
  }

  /** Per-GPU rate for a hardware choice.
   *  - benchmarked hardware: its reported rate × multiplier (multiplier > 1 is a what-if, marked "assumed").
   *  - unbenchmarked hardware (H200/B200): NO rate unless the user picks an explicit multiplier of the
   *    reference GPU's rate; the result is then "assumed", never "measured".
   *  - custom: the user's own rate. */
  function scenarioRate(cfg, sel) {
    var hw = findHw(cfg, sel.hardware);
    var ref = findHw(cfg, (cfg && cfg.reference_hardware) || "rtx5090");
    var m = sel.multiplier == null ? null : Number(sel.multiplier);
    if (m != null && !(isFinite(m) && m > 0)) fail("speed multiplier must be a positive number");
    if (!hw) return { known: false, basis: "unknown", reason: "unknown hardware" };
    if (hw.id === "custom") {
      var r = Number(sel.customRate);
      if (!(isFinite(r) && r > 0)) return { known: false, basis: "unknown", reason: "enter a measured rate" };
      return { known: true, basis: "custom", rate: r, hw: hw };
    }
    if (hw.benchmarked && hw.ops_per_sec > 0) {
      var mm = m == null ? 1 : m;
      return { known: true, basis: mm === 1 ? "measured" : "assumed", rate: hw.ops_per_sec * mm, multiplier: mm, hw: hw };
    }
    // Unbenchmarked: unknown until the user states an assumption.
    if (m == null || !ref || !(ref.ops_per_sec > 0)) return { known: false, basis: "unknown", reason: "no benchmark for this workload", hw: hw };
    return { known: true, basis: "assumed", rate: ref.ops_per_sec * m, multiplier: m, hw: hw, relativeTo: ref };
  }

  function scenario(cfg, sel) {
    var rate = scenarioRate(cfg, sel);
    var l10 = (sel.log2Work == null ? 128 : Number(sel.log2Work)) * LOG10_2;
    var out = { rate: rate, log10Ops: l10, gpus: sel.gpus };
    if (rate.known) out.result = estimate(l10, sel.gpus, rate.rate);
    return out;
  }

  /** Baseline (published reference) vs current best research result in the SAME units.
   *  Only a curated, reviewed entry (cfg.current_result) with comparable units can differ from the
   *  baseline; outcome keyword claims alone never change the number. */
  function comparison(cfg, outcome) {
    var base = (cfg && cfg.default_log2_work) || 128;
    var cur = cfg && cfg.current_result;
    var ok = !!(cur && cur.reviewed === true && cur.units === "group operations" &&
      isFinite(cur.log2_work) && cur.log2_work > 0 && cur.source);
    var status = (outcome && outcome.status) || "unknown";
    return {
      baselineLog2: base,
      currentLog2: ok ? cur.log2_work : base,
      changed: ok && cur.log2_work !== base,
      validated: ok,
      outcomeStatus: status,
      pendingClaim: !ok && (status === "reported_positive" || status === "conflicting")
    };
  }

  var BIG = [[3, "thousand"], [6, "million"], [9, "billion"], [12, "trillion"], [15, "quadrillion"],
             [18, "quintillion"], [21, "sextillion"], [24, "septillion"], [27, "octillion"], [30, "nonillion"], [33, "decillion"]];
  function roundSig(x) { return x >= 100 ? Math.round(x) : Math.round(x * 10) / 10; }
  /** Human-readable count from log10: 559 → "559", 5.59e14 → "559 trillion". Beyond decillions: "10^N". */
  function humanNumber(l10) {
    if (!isFinite(l10)) return "—";
    if (l10 < 0) return String(Number(Math.pow(10, l10).toPrecision(2)));
    if (l10 < 3) return roundSig(Math.pow(10, l10)).toLocaleString("en-US");
    if (l10 < 6) { var q = Math.pow(10, Math.floor(l10) - 2); return (Math.round(Math.pow(10, l10) / q) * q).toLocaleString("en-US"); }
    for (var i = BIG.length - 1; i >= 0; i--) {
      if (l10 >= BIG[i][0] && l10 < BIG[i][0] + 3) return roundSig(Math.pow(10, l10 - BIG[i][0])).toLocaleString("en-US") + " " + BIG[i][1];
    }
    return "10^" + Math.floor(l10);
  }
  /** Human-readable duration from log10(years): "559 trillion years", "3.2 days", "40 seconds". */
  function humanYears(l10y) {
    if (!isFinite(l10y)) return "—";
    if (l10y >= 0) { var n = humanNumber(l10y); return n + (n === "1" ? " year" : " years"); }
    var s = Math.pow(10, l10y) * SECONDS_PER_YEAR;
    var units = [[86400, "day"], [3600, "hour"], [60, "minute"], [1, "second"]];
    for (var j = 0; j < units.length; j++) if (s >= units[j][0]) { var v = roundSig(s / units[j][0]); return v + " " + units[j][1] + (v === 1 ? "" : "s"); }
    return "under a second";
  }

  var api = { parseNumber: parseNumber, workLog10: workLog10, estimate: estimate, sci: sci,
              scenarioRate: scenarioRate, scenario: scenario, comparison: comparison, humanYears: humanYears, humanNumber: humanNumber,
              SECONDS_PER_YEAR: SECONDS_PER_YEAR, LOG10_2: LOG10_2, AGE_OF_UNIVERSE_YEARS: 1.38e10 };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.Estimator = api;
})(typeof window !== "undefined" ? window : this);
