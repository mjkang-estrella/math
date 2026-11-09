"""shrink-review-r1: random points of the cycle polytope (averages of q random simple cycles,
hence in P_A) on n vertices; non-confluence of S1S2 under V1/V2/V3 (see variant_search.py).
usage: variant_sample.py seed samples"""
import sys, random, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from variant_search import St

def sample(rng, n, q):
    Y = [0] * n; X = {}
    for _ in range(q):
        L = rng.randint(3, n)
        cyc = rng.sample(range(n), L)
        for v in cyc: Y[v] += 1
        for i in range(L):
            a, b = sorted((cyc[i], cyc[(i + 1) % L]))
            X[(a, b)] = X.get((a, b), 0) + 1
    return Y, X

def main():
    seed, ns = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    stats = {}
    ex = []
    for it in range(ns):
        n = rng.randint(6, 9); q = rng.randint(2, 4)
        Y, X = sample(rng, n, q)
        if min(Y) == 0:
            continue                 # isolated vertices: skip (they never take part)
        st = St(n, Y, X)
        for var in ["V1", "V2", "V3"]:
            depots = [None] if var != "V3" else [v for v in range(n) if Y[v] == q][:1]
            for d in depots:
                T = st.explore(var, d)
                s = stats.setdefault(var, [0, 0])
                s[0] += 1
                if len(T) > 1 and (len(set(st.inv(P) for P in T)) > 1 or len(set(st.canon(P) for P in T)) > 1):
                    s[1] += 1
                    if var != "V1" and len(ex) < 5:
                        ex.append({"var": var, "n": n, "q": q, "Y": Y, "X": {"%d-%d" % k: v for k, v in X.items()}, "depot": d})
    print(json.dumps({"seed": seed, "samples": ns, "stats(inputs,nonconfluent)": stats, "non_V1_examples": ex}))

main()
