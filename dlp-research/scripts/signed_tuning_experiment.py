"""Finite public-width tuning audit of W006's unchanged BSGS engines.

Every scalar is tested at every allowed width on the three smallest W004
curves. Dominance concerns sums of the five instrumented event classes only;
no runtime, memory, hardware, asymptotic or full-cost dominance is inferred.
"""
from dataclasses import asdict
from math import isqrt
import json

from signed_bsgs_experiment import Curve, SignedCost, solve


def dominates(left, right):
    return (all(left[k] <= right[k] for k in left)
            and any(left[k] < right[k] for k in left))


def main():
    curves = [Curve(5, 2, 1, (0, 1), 7), Curve(17, 2, 2, (0, 6), 19),
              Curve(43, 0, 7, (2, 12), 31)]
    output = []
    total_events = 0
    total_cases = 0
    for curve in curves:
        assert all(curve.p % d for d in range(2, isqrt(curve.p)+1))
        assert (4*curve.a**3 + 27*curve.b**2) % curve.p != 0
        points = {None} | {(x, y) for x in range(curve.p) for y in range(curve.p)
                          if (y*y-x**3-curve.a*x-curve.b) % curve.p == 0}
        orbit = []
        current = None
        for _ in range(curve.q):
            assert current in points and current not in orbit
            orbit.append(current)
            current = curve.add(current, curve.generator)
        assert current is None and set(orbit) == points
        rows = []
        for signed in [False, True]:
            max_m = (curve.q+1)//2 if signed else curve.q
            for m in range(1, max_m+1):
                totals = {k: 0 for k in SignedCost.__dataclass_fields__}
                for d, target in enumerate(orbit):
                    answer, cost = solve(curve, target, m, signed)
                    assert answer == d, (curve, signed, m, d, answer)
                    sample = asdict(cost)
                    for k, value in sample.items():
                        totals[k] += value
                    total_events += sum(sample.values())
                    total_cases += 1
                    assert total_events <= 1_000_000
                rows.append({"variant": "signed" if signed else "ordinary",
                             "m": m, "totals_all_secrets": totals})
        for row in rows:
            row["dominated_by"] = [
                {"variant": other["variant"], "m": other["m"]}
                for other in rows if dominates(other["totals_all_secrets"],
                                                row["totals_all_secrets"])]
        default_m = isqrt((curve.q-1)//2)+1
        default = next(r for r in rows if r["variant"] == "signed" and r["m"] == default_m)
        proxies = []
        for add_weight in [1, 4, 16, 64]:
            def score(row):
                totals = row["totals_all_secrets"]
                return sum(totals.values()) + (add_weight-1)*totals["adds"]
            minimum = min(score(row) for row in rows)
            proxies.append({"add_weight": add_weight, "other_event_weights": 1,
                            "minimum_proxy_sum": minimum,
                            "minimizers": [{"variant": row["variant"], "m": row["m"]}
                                           for row in rows if score(row) == minimum]})
        output.append({"curve": asdict(curve), "widths_tested": len(rows),
                       "signed_sqrt_half_default": default,
                       "uncalibrated_proxy_sensitivity": proxies,
                       "rows": rows})
    print(json.dumps({"scope": "finite event-vector sums only; every scalar; fresh preprocessing",
                      "excluded": "field/bit work, key creation, access/allocation, peak memory, timing",
                      "counted_events": total_events, "scalar_width_cases": total_cases,
                      "results": output}, indent=2))


if __name__ == "__main__":
    main()
