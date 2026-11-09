# ablation variant of pdsat.py (MODE env: all|noA|noB|pairsonly|nopd)
"""353203: is K_{s,t} the only graph (no isolated vertices) on V=A u B whose power dominating sets are exactly those of K_{s,t}?
By Bong-Carlson-Curtis-Haas-Hogben (Graphs Combin. 2023) / survey arXiv:2406.05509 Thm t:main, PD-TAR(G) ~= PD-TAR(K_{s,t})
iff (after relabeling) G has exactly the PD sets of K_{s,t}.  PD sets are up-closed, so equality of families <=>
 (i) every minimal PD set of K_{s,t} is PD in G  [encoded by a time-indexed forcing chronology], and
 (ii) every maximal non-PD set of K_{s,t} is non-PD in G  [encoded by a fort disjoint from N[S]].
A fort F: nonempty, and every vertex outside F has 0 or >=2 neighbours in F.  S is not PD iff some fort misses N[S].
Plus: no isolated vertex, and E(G) != E(K_{A,B}).  UNSAT => uniqueness for this (s,t).
usage: pdsat.py s t out.cnf  -> writes DIMACS; prints var map summary."""
import sys, itertools
s, t = int(sys.argv[1]), int(sys.argv[2]); out = sys.argv[3]
n = s + t; A = list(range(s)); B = list(range(s, n))
nv = 0; cls = []
def new():
    global nv; nv += 1; return nv
E = {}
for u, v in itertools.combinations(range(n), 2): E[(u, v)] = E[(v, u)] = new()
def e(u, v): return E[(u, v)]
# minimal PD sets of K_{s,t}
minPD = [frozenset([a, b]) for a in A for b in B]
if s >= 2: minPD += [frozenset(c) for c in itertools.combinations(A, s - 1)]
if t >= 2: minPD += [frozenset(c) for c in itertools.combinations(B, t - 1)]
# maximal non-PD sets: (s-2)-subsets of A, (t-2)-subsets of B (s,t >= 3); also any single... covered.
maxNon = [frozenset(c) for c in itertools.combinations(A, s - 2)] + [frozenset(c) for c in itertools.combinations(B, t - 2)]
def pd(S):
    T = n  # rounds
    obs = [[new() for v in range(n)] for k in range(T + 1)]
    for v in range(n):
        if v in S: cls.append([obs[0][v]]); continue
        # obs0[v] -> OR_{u in S} e(u,v)
        cls.append([-obs[0][v]] + [e(u, v) for u in S])
    for k in range(T):
        for v in range(n):
            fs = []
            for u in range(n):
                if u == v: continue
                f = new(); fs.append(f)
                cls.append([-f, obs[k][u]]); cls.append([-f, e(u, v)])
                for w in range(n):
                    if w in (u, v): continue
                    cls.append([-f, -e(u, w), obs[k][w]])
            cls.append([-obs[k + 1][v], obs[k][v]] + fs)
    for v in range(n): cls.append([obs[T][v]])
def nonpd(S):
    x = [new() for v in range(n)]
    cls.append(x[:])  # nonempty
    for v in range(n):
        if v in S: cls.append([-x[v]])
        for u in S:
            if u != v: cls.append([-x[v], -e(u, v)])
    # y[u][w] -> x[w] & e(u,w)
    y = {}
    for u in range(n):
        for w in range(n):
            if u == w: continue
            yy = new(); y[(u, w)] = yy; cls.append([-yy, x[w]]); cls.append([-yy, e(u, w)])
    for u in range(n):
        for v in range(n):
            if u == v: continue
            cls.append([x[u], -x[v], -e(u, v)] + [y[(u, w)] for w in range(n) if w not in (u, v)])
import os
MODE=os.environ.get('MODE','all')
for S in minPD:
    if MODE in ('all','noA','noB','pairsonly') and (MODE!='pairsonly' or len(S)==2 and (min(S)<s)!=(max(S)<s)): pd(S)
    elif MODE=='nopd': pass
for S in maxNon:
    if MODE=='noA' and max(S,default=0)<s: continue
    if MODE=='noB' and min(S,default=n)>=s: continue
    nonpd(S)
for v in range(n): cls.append([e(u, v) for u in range(n) if u != v])
diff = [e(u, v) for u, v in itertools.combinations(A, 2)] + [e(u, v) for u, v in itertools.combinations(B, 2)] + [-e(a, b) for a in A for b in B]
cls.append(diff)
with open(out, 'w') as f:
    f.write(f'p cnf {nv} {len(cls)}\n')
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
print(f's={s} t={t} vars={nv} clauses={len(cls)} minPD={len(minPD)} maxNonPD={len(maxNon)}')
