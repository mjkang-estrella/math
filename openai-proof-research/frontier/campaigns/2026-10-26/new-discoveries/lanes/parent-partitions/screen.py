"""Exact overpartition coefficient and array-line search; no proof claim."""
from pathlib import Path
from functools import lru_cache
from math import comb, factorial, gcd
import json
import sys
sys.path.insert(0, str(Path('../polynomial/.pydeps').resolve()))
from flint import fmpz_poly


@lru_cache(None)
def gaussian(n, k):
    if k < 0 or k > n:
        return fmpz_poly([])
    if k in [0, n]:
        return fmpz_poly([1])
    if 2*k > n:
        return gaussian(n, n-k)
    return gaussian(n-1, k) + gaussian(n-1, k-1).left_shift(n-k)


def unimodal(values):
    descending = False
    for a, b in zip(values, values[1:]):
        if b < a:
            descending = True
        if descending and b > a:
            return False
    return True


tested = 0
stronger_failures = []
for bound in range(2, 36):
    for m in range(2, bound+1):
        n = bound
        polys = [(gaussian(m, k)*gaussian(m+n-k, n-k)).left_shift(k*(k+1)//2)
                 for k in range(m+1)]
        for size in range(m*n+1):
            row = [int(p[size]) for p in polys]
            tested += 1
            if not unimodal(row):
                hit = {"M": m, "N": n, "size": size, "coefficients": row,
                       "status": "EXACT HIT; source/novelty/independent/Lean gates pending"}
                Path('hit.json').write_text(json.dumps(hit, indent=2)+'\n')
                print(json.dumps(hit), flush=True)
                raise SystemExit
            f = [factorial(k)*b for k, b in enumerate(row)]
            if all(f[k]**2 >= f[k-1]*f[k+1] for k in range(1, m)):
                continue
            stronger_failures.append({"M": m, "N": n, "size": size, "row": row})
            # This stronger log-concavity suffices for every array-line
            # log-concavity, but failure alone does not refute unimodality.
            array = {(i,j): comb(i+j,i)*row[i+j]
                     for i in range(m+1) for j in range(m+1-i)}
            for dx in range(0, m+1):
                for dy in range(-m, m+1):
                    if gcd(dx,dy) != 1 or (dx == 0 and dy <= 0):
                        continue
                    for start in array:
                        if (start[0]-dx, start[1]-dy) in array:
                            continue
                        point = start
                        values, points = [], []
                        while point in array:
                            values.append(array[point]); points.append(list(point))
                            point = (point[0]+dx, point[1]+dy)
                        if not unimodal(values):
                            hit = {"M": m, "N": n, "size": size, "row": row,
                                   "direction": [dx,dy], "points": points, "cut": values,
                                   "status": "EXACT ARRAY-LINE HIT; independent/source/novelty/Lean gates pending"}
                            Path('hit.json').write_text(json.dumps(hit, indent=2)+'\n')
                            print(json.dumps(hit), flush=True)
                            raise SystemExit
    print(bound, tested, len(stronger_failures), flush=True)
output = {"status": "No unimodality violation found; finite exact scan only",
          "boxes": "2<=M<=N<=35", "size_sequences": tested,
          "stronger_factorial_log_concavity_failures": stronger_failures}
Path('screen.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps({k:v for k,v in output.items() if k != 'stronger_factorial_log_concavity_failures'}))
