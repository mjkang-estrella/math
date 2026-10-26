"""Exact exploratory check of published Conjecture 7.5; not a proof."""
import argparse
import json
import time
from pathlib import Path


def interval_product(p, length):
    if not p:
        return []
    out = []
    total = 0
    for j in range(len(p) + length - 1):
        if j < len(p):
            total += p[j]
        if j >= length:
            total -= p[j-length]
        out.append(total)
    return out


def plus(a, b):
    out = a[:] + [0] * max(0, len(b)-len(a))
    for j, x in enumerate(b):
        out[j] += x
    return out


def run(limit):
    start = time.time()
    checks = 0
    rows = {"S": [[1]], "c": [[1]]}
    for n in range(1, limit+1):
        for kind, old in list(rows.items()):
            new = []
            for k in range(n+1):
                p = plus(old[k-1] if k else [], interval_product(
                    old[k] if k < n else [], 2*k+1 if kind == "S" else 2*n-1))
                for j in range(2, len(p)-2):
                    checks += 1
                    if p[j]**2 < p[j-2]*p[j+2]:
                        return {"status":"COUNTEREXAMPLE", "kind":kind,
                                "n":n,"k":k,"degree":j,
                                "values":[p[j-2],p[j],p[j+2]],
                                "elapsed":time.time()-start,"checks":checks}
                new.append(p)
            rows[kind] = new
        if n % 10 == 0:
            print(n, checks, round(time.time()-start, 2), flush=True)
    assert rows["S"][limit] == [1]
    return {"status":"NO_COUNTEREXAMPLE_IN_FINITE_SEARCH", "max_n":limit,
            "checks":checks,"elapsed":time.time()-start,
            "definition":"S[n,k]=S[n-1,k-1]+[2k+1]S[n-1,k]; c[n,k]=c[n-1,k-1]+[2n-1]c[n-1,k]",
            "claim":"No discovery credit and no universal conclusion."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit",type=int,default=120)
    args=parser.parse_args()
    result=run(args.limit)
    Path(__file__).with_name("search-result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result),flush=True)
