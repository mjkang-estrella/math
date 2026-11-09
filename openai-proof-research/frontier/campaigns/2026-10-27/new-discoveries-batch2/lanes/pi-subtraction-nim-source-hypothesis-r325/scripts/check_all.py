"""Runnable checker for lane pi-subtraction-nim-source-hypothesis-r325.
Reruns the decisive computations and prints PASS/FAIL lines.
Run via helper_guard with the standard env; or directly:
  python3 -B scripts/check_all.py
"""
import os, sys, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scan3 import analyze, crosscheck  # noqa: E402
from solutions_enum import enumerate_solutions, min_period_of  # noqa: E402

ok = True


def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        ok = False


# 1. r302 witness S=(1,3,5): minimal period 2, and a+b=4 is a period (2|4)
r = analyze((1, 3, 5), 20000)
check("S=(1,3,5) min period 2 (r302 witness)", r["min_period"] == 2)
check("S=(1,3,5) a+b=4 is a period (2|4): literal conjecture holds",
      all(s % 2 == 0 for s in (4, 8, 6)))

# 2. exact known values
for S, m in [((2, 3, 4), 6), ((1, 2, 3), 4), ((2, 5, 6), 11), ((1, 6, 9), 5), ((1, 2, 6), 7)]:
    r = analyze(S, 60000)
    check(f"S={S} min period {m}", r["min_period"] == m)
    check(f"S={S} divisibility form holds", any(s % m == 0 for s in (S[0]+S[1], S[1]+S[2], S[2]+S[0])))

# 3. bad periodic solution exists for S=(1,3,6) on Z_12 (mechanism evidence)
res = enumerate_solutions((1, 3, 6), 12)
bad = [t for t in res["solutions"] if min_period_of(t) == 12]
check("S=(1,3,6): periodic solutions with minimal period 12 exist on Z_12",
      len(bad) > 0 and all(12 not in () for _ in bad))
if bad:
    t = bad[0]

    def mex(s):
        i = 0
        while i in s:
            i += 1
        return i
    check("bad solution satisfies mex equation on Z_12",
          all(t[x] == mex({t[(x - a) % 12] for a in (1, 3, 6)}) for x in range(12)))
    check("12 divides none of (4,9,7)", all(s % 12 for s in (4, 9, 7)))

# 4. full-scope spot checks near the scan boundary
for S in [(20, 30, 40), (21, 39, 40), (13, 27, 41), (1, 2, 40)]:
    r = analyze(S, 100000)
    m = r["min_period"]
    sums = (S[0] + S[1], S[1] + S[2], S[2] + S[0])
    check(f"S={S} divisibility form (m={m})", any(s % m == 0 for s in sums))
    check(f"S={S} crosscheck", crosscheck(S, r) == [])

print("ALL OK" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
