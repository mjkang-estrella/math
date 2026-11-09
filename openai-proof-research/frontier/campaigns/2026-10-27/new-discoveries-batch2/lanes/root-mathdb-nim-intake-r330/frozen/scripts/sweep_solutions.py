"""Sweep: for all 0<a<b<c<=B, c!=a+b, enumerate all periodic solutions of the
mex functional equation on Z_L for L<=Lmax; report triples having any solution
whose minimal period divides no pairwise sum (bad), vs the game's own period.
"""
import sys, json, math
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from solutions_enum import enumerate_solutions, min_period_of
from scan2 import analyze


def main():
    B = int(sys.argv[1]); Lmax = int(sys.argv[2])
    rows = []
    n_bad_triples = 0
    for a in range(1, B + 1):
        for b in range(a + 1, B + 1):
            for c in range(b + 1, B + 1):
                if c == a + b:
                    continue
                S = (a, b, c)
                sums = (a + b, b + c, c + a)
                r = analyze(S, 6000)
                m_game = r["min_period"] if r else None
                bad_L = []
                all_L = []
                for L in range(1, Lmax + 1):
                    res = enumerate_solutions(S, L)
                    if res is None or not res["solutions"]:
                        continue
                    if res.get("note") == "node_cap_exceeded":
                        all_L.append([L, "CAP"])
                        continue
                    pers = sorted({min_period_of(t) for t in res["solutions"]})
                    all_L.append([L, pers])
                    if any(all(s % p for s in sums) for p in pers):
                        bad_L.append([L, [p for p in pers if all(s % p for s in sums)]])
                if bad_L:
                    n_bad_triples += 1
                rows.append({"S": list(S), "sums": list(sums), "game_m": m_game,
                             "solutions_by_L": all_L, "bad": bad_L})
    print(json.dumps({"B": B, "Lmax": Lmax, "n_triples": len(rows),
                      "n_triples_with_bad_solutions": n_bad_triples,
                      "rows": rows}))
    with open(sys.argv[3], "w") as f:
        json.dump({"B": B, "Lmax": Lmax, "rows": rows}, f)


if __name__ == "__main__":
    main()
