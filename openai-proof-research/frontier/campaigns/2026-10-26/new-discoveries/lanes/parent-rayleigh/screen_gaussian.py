"""Exact finite screen, Amdeberhan--Callan Conjecture 4 / published 15."""
from pathlib import Path
import json
import sys
from functools import lru_cache
sys.path.insert(0, str(Path('../polynomial/.pydeps').resolve()))
from flint import fmpz_poly


@lru_cache(None)
def gaussian(n, k):
    if k < 0 or k > n:
        return fmpz_poly([])
    if k in [0, n]:
        return fmpz_poly([1])
    if 2 * k > n:
        return gaussian(n, n-k)
    return gaussian(n-1, k) + gaussian(n-1, k-1).left_shift(n-k)


count = 0
for b in range(2, 46):
    for a in range(1, b):
        for k in range(1, a+1):
            difference = gaussian(a, k) * gaussian(a+b, b-k) - gaussian(b, k) * gaussian(a+b, a-k)
            count += 1
            if any(c < 0 for c in difference):
                hit = {"a": a, "b": b, "k": k, "coefficients": list(map(int, difference)),
                       "status": "Exact hit; source/independent/novelty/formal gates pending"}
                Path('gaussian-hit.json').write_text(json.dumps(hit, indent=2) + '\n')
                print(json.dumps(hit), flush=True)
                raise SystemExit
    if b % 10 == 0:
        print(b, count, flush=True)
output = {"status": "No negative coefficient found; not a proof", "range": "1<=k<=a<b<=45",
          "triples": count, "arithmetic": "FLINT exact integer polynomials with Gaussian recurrence"}
Path('gaussian-screen.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output))
