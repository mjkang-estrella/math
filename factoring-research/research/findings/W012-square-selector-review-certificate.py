"""Only the fixed algebra certificates in the separately frozen brief; no sweep."""
from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json

PREFIX = Path(__file__).with_name("W012-square-selector-review")
checks = []


def check(name, actual, expected):
    checks.append({"name": name, "actual": actual, "expected": expected,
                   "passed": actual == expected})


def ceil_root(n, v):
    return isqrt((n - 1) // v) + 1


def select(n, b, j):
    """Find the last k with g_k >= j+1; callers validate the slope range."""
    def g(k):
        return ceil_root(n, k - 1) - ceil_root(n, k)
    lo, hi = 2, b
    probes = []
    while hi - lo > 1:
        mid = (lo + hi) // 2
        value = g(mid)
        probes.append({"mid": mid, "g": value})
        if value >= j + 1:
            lo = mid
        else:
            hi = mid
    return lo, probes


n, b = 100001, 4
tv = [ceil_root(n, v) for v in (1, 2, 3, 4)]
check("fixed ceiling roots", tv, [317, 224, 183, 159])
check("curvature integer guard", 9*n > 64*(b+1)**5, True)
residuals = []
for v, t in zip((1, 2, 3, 4), tv):
    r = v*t*t - n
    residuals.append(r)
    check(f"v={v} ceiling minimality", v*(t-1)**2 < n <= v*t*t, True)
    check(f"v={v} congruence", ((v*t)**2-v*r) % n, 0)
    # If r-v < 0, (2) is immediate; otherwise square its positive sides.
    check(f"v={v} strict residual bound", r >= 0 and
          (r-v < 0 or (r-v)**2 < 4*n*v), True)
g2, g3, g4 = tv[0]-tv[1], tv[1]-tv[2], tv[2]-tv[3]
w2, w3 = g2-g3, g3-g4
width = g2-g4
check("g sequence", [g2, g3, g4], [93, 41, 24])
check("normal interval widths", [w2, w3, width], [52, 17, 69])
check("telescoping widths", w2+w3, width)
bins = {"2": [g3, g2-1], "3": [g4, g3-1]}
check("algebraic bin cardinalities", [bins['2'][1]-bins['2'][0]+1,
      bins['3'][1]-bins['3'][0]+1], [52, 17])
probes = []
for j, expected in ((24, 3), (40, 3), (41, 2), (92, 2)):
    v, trace = select(n, b, j)
    check(f"binary-search endpoint J={j}", v, expected)
    probes.append({"J": j, "selected": v, "trace": trace})
    objective = [2*t+(2*j+1)*x for x, t in zip((1, 2, 3, 4), tv)]
    check(f"unique global objective minimum J={j}",
          [i+1 for i, z in enumerate(objective) if z == min(objective)], [expected])
for j, expected in ((23, 4), (93, 1)):
    objective = [2*t+(2*j+1)*x for x, t in zip((1, 2, 3, 4), tv)]
    check(f"excluded endpoint slope J={j}",
          [i+1 for i, z in enumerate(objective) if z == min(objective)], [expected])
prob = Fraction(w2, width)
check("probability is non-dyadic", prob.denominator & (prob.denominator-1) != 0, True)
check("B=3 unique interior vertex", select(n, 3, 41)[0], 2)
check("B=2 zero normalizer", g2-g2, 0)

outside = [ceil_root(15, v) for v in (1, 2, 3, 4, 5)]
check("outside-regime roots", outside, [4, 3, 3, 2, 2])
check("outside-regime negative second difference", outside[1]-2*outside[2]+outside[3], -1)
obj = [2*t+v for v, t in zip((1, 2, 3, 4, 5), outside)]
check("outside-regime half-integer tie", [i+1 for i,z in enumerate(obj) if z == min(obj)], [2, 4])
check("truncated quotient trap", ceil_root(19, 2), 4)
check("exact-square trap", ceil_root(18, 2), 3)
mid_r = Fraction(5, 2)*Fraction(9, 2)**2-36
check("zero residual endpoints", [1*6**2-36, 4*3**2-36], [0, 0])
check("nonconvex zero-residual midpoint", str(mid_r), "117/8")
check("retained zero residual", 5*ceil_root(45, 5)**2-45, 0)
check("zero-residual proper gcd", gcd(5, 45), 5)

brief = Path(str(PREFIX)+"-certificate-brief.md")
report = {"scope": "fixed algebra only; no sampled slopes or performance experiments",
          "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
          "brief_sha256": sha256(brief.read_bytes()).hexdigest(),
          "fixed_case_residuals": residuals, "bins_inclusive": bins,
          "binary_search_traces": probes, "checks": checks,
          "total": len(checks), "failed": sum(not x['passed'] for x in checks)}
out = Path(str(PREFIX)+"-certificate-output.json")
with out.open('x') as f:
    json.dump(report, f, indent=2)
    f.write('\n')
print(json.dumps({"output": str(out), "checks": report['total'], "failed": report['failed']}))
raise SystemExit(bool(report['failed']))
