"""Recheck all 37 r302 witnesses for 375237 under the source's literal
(non-minimal period) reading. Exact state-cycle method.
Usage: recheck_r302.py out.json
"""
import sys, json, os

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESS = os.path.join(LANE, "..", "pi-mathdb-finite-arithmetic-triage-r302",
                       "screening", "witness-375237.json")
sys.path.insert(0, os.path.join(LANE, "scripts"))
from scan3 import analyze  # noqa: E402


def main():
    wit = json.load(open(WITNESS))
    out = []
    for w in wit["witnesses_first_40"]:
        S = tuple(w["S"])
        r = analyze(S, 60000)
        m = r["min_period"]
        sums = w["claimed_set"]
        out.append({"S": list(S), "r302_eventual_period": w["eventual_period"],
                    "exact_min_period": m, "preperiod": r["preperiod"],
                    "sums": sums,
                    "divides_some_sum": any(s % m == 0 for s in sums),
                    "literal_conjecture_holds": any(s % m == 0 for s in sums)})
    res = {"source": WITNESS, "n": len(out),
           "all_literal_hold": all(o["literal_conjecture_holds"] for o in out),
           "witnesses": out}
    print(json.dumps({k: res[k] for k in ("n", "all_literal_hold")}))
    with open(sys.argv[1], "w") as f:
        json.dump(res, f)


if __name__ == "__main__":
    main()
