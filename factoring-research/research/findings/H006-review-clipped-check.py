"""Check interior certificates on actual clipped Card 1 boxes; review-only output."""
import hashlib
import json
import math
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "H006-review-clipped-check.json"
HELPER = HERE / "H006-review-audit.py"
namespace = {"__name__": "H006_review_helper", "__file__": str(HELPER)}
exec(compile(HELPER.read_text(), str(HELPER), "exec"), namespace)
coefficients = namespace["coefficients"]
bounds = namespace["independent_bounds"]


def main():
    if OUT.exists():
        raise SystemExit("Refusing to overwrite review evidence")
    start = time.monotonic()
    frozen = json.loads((HERE.parent / "experiments/H006/result.json").read_text())
    rows = []
    for original in frozen["rows"]:
        if original["K"] != 36:
            continue
        n, s = original["n"], original["s"]
        r, m, modulus = 2**s, 2**(3*s), 2**(6*s)
        plo, phi = m//2, math.isqrt(n)
        qlo, qhi = (n+m-1)//m, (2*n)//m
        counts = {"odd_positions": 0, "qualifying_positions": 0,
                  "frontier_nodes": 0, "frontier_endpoints": 0,
                  "qualifying_interior_positions": 0, "certified_frontier_nodes": 0}
        example = None
        for a in range(1, r, 2):
            root_left, root_right = (plo-a+r-1)//r, (phi-a)//r
            assert root_right-root_left+1 >= 16
            c = coefficients(n, s, a)
            stack = [(root_left, root_right)]
            while stack:
                left, right = stack.pop()
                if right-left+1 >= 32:
                    mid = (left+right)//2
                    stack.extend(((left, mid), (mid+1, right)))
                    continue
                assert 16 <= right-left+1 <= 31
                counts["frontier_nodes"] += 1
                counts["frontier_endpoints"] += 2
                good_node = False
                for t in range(left, right+1):
                    p = a+r*t
                    assert plo <= p <= phi
                    counts["odd_positions"] += 1
                    q = n*pow(p, -1, m) % m
                    if not qlo <= q <= qhi:
                        continue
                    counts["qualifying_positions"] += 1
                    if t in (left, right):
                        continue
                    counts["qualifying_interior_positions"] += 1
                    z = [1, t, t*t]
                    for j in range(3, 6):
                        partial = sum(x*y for x,y in zip(c,z))
                        assert (q-partial) % r**j == 0
                        residue = (q-partial)//r**j * pow(c[j]//r**j, -1, r) % r
                        low, high = bounds(j,t,left,right)
                        value = low+(residue-low)%r
                        assert value <= high
                        z.append(value)
                    assert (sum(x*y for x,y in zip(c,z))-q) % modulus == 0
                    anc_left, anc_right = root_left, root_right
                    while True:
                        assert all(bounds(j,t,anc_left,anc_right)[0] <= z[j] <= bounds(j,t,anc_left,anc_right)[1] for j in range(2,6))
                        if (anc_left, anc_right) == (left, right):
                            break
                        mid = (anc_left+anc_right)//2
                        if right <= mid:
                            anc_right=mid
                        else:
                            assert left > mid
                            anc_left=mid+1
                    if not good_node:
                        counts["certified_frontier_nodes"] += 1
                    good_node = True
                    if example is None:
                        example = {"a":a,"left":left,"right":right,"t":t,"q":q,"z":z}
        rows.append({"n":n,"K":36,"I":[plo,phi],"J":[qlo,qhi],"counts":counts,
                     "witness_example":example,"three_times_frontier_lower_bound":3*counts["certified_frontier_nodes"]})
    out = {"status":"all_checks_passed", "rows":rows,
           "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "helper_sha256":hashlib.sha256(HELPER.read_bytes()).hexdigest(),
           "seconds":time.monotonic()-start,
           "scope":"Exhaustive-tree diagnostic only; exponential enumeration cost is not an algorithmic gain."}
    OUT.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"status":out["status"],"seconds":out["seconds"],"counts":[r["counts"] for r in rows]}))


if __name__ == "__main__":
    main()
