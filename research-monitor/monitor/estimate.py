"""Rough runtime arithmetic, computed in log10 space so 2^256 never overflows.

This mirrors static/estimator.js (tested against the same reference values).
It is a conditional calculation: work / (gpus * rate), assuming perfect linear
scaling, full utilization and no communication or memory overhead.
"""

from __future__ import annotations

import math

SECONDS_PER_DAY = 86_400.0
SECONDS_PER_YEAR = 365.25 * SECONDS_PER_DAY  # Julian year
LOG10_2 = math.log10(2.0)
MAX_LOG2_WORK = 4096.0


class EstimateError(ValueError):
    pass


def work_log10(*, log2_work: float | None = None, sci_work: float | None = None) -> float:
    if (log2_work is None) == (sci_work is None):
        raise EstimateError("give exactly one of log2_work or sci_work")
    if log2_work is not None:
        if not math.isfinite(log2_work) or log2_work < 0 or log2_work > MAX_LOG2_WORK:
            raise EstimateError(f"log2 work must be within [0, {MAX_LOG2_WORK:g}]")
        return log2_work * LOG10_2
    if not math.isfinite(sci_work) or sci_work < 1:
        raise EstimateError("work must be a finite number >= 1")
    return math.log10(sci_work)


def estimate(log10_ops: float, gpus: float, ops_per_sec_per_gpu: float) -> dict:
    for name, v in (("gpus", gpus), ("ops_per_sec_per_gpu", ops_per_sec_per_gpu)):
        if not math.isfinite(v) or v <= 0:
            raise EstimateError(f"{name} must be a positive finite number")
    log10_rate = math.log10(gpus) + math.log10(ops_per_sec_per_gpu)
    log10_seconds = log10_ops - log10_rate
    log10_years = log10_seconds - math.log10(SECONDS_PER_YEAR)
    return {
        "log10_ops": log10_ops,
        "log2_ops": log10_ops / LOG10_2,
        "log10_seconds": log10_seconds,
        "log10_days": log10_seconds - math.log10(SECONDS_PER_DAY),
        "log10_years": log10_years,
        "log10_gpu_years": log10_years + math.log10(gpus),
        "seconds": sci(log10_seconds),
        "days": sci(log10_seconds - math.log10(SECONDS_PER_DAY)),
        "years": sci(log10_years),
        "gpu_years": sci(log10_years + math.log10(gpus)),
    }


def sci(log10_value: float, digits: int = 3) -> str:
    """Format 10**log10_value in scientific notation without evaluating it."""
    exp = math.floor(log10_value)
    mant = 10 ** (log10_value - exp)
    if round(mant, digits - 1) >= 10:
        mant, exp = mant / 10, exp + 1
    return f"{mant:.{digits - 1}f}e{exp:+d}"
