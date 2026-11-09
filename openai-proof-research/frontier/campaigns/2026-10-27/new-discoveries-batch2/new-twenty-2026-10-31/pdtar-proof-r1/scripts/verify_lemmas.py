"""Exhaustive sanity checks of the PROOF.md lemmas on ALL graphs on A u B with |A|=s, |B|=t (chunked).
Each lemma is checked under exactly the hypotheses its proof uses (often weaker than the full hypothesis),
and the number of non-vacuous instances is reported.

Hypothesis flags of a graph H on V = A u B:
  noiso : no isolated vertex
  C1    : every minimal PD set of K_{A,B} is PD in H (cross pairs, (s-1)-subsets of A, (t-1)-subsets of B)
  NA    : every (s-2)-subset of A is non-PD in H;  NB : same for B
Lemmas (numbering as in PROOF.md):
  L0  fort duality: S is PD  <=>  no fort F with F & N[S] empty                       (all graphs, all S)
  L1  C1 => every fort F has [A in N[F] and |N[F]&B|>=2] or [B in N[F] and |N[F]&A|>=2]
  L2  C1 & NA & noiso => every a in A has a B-neighbour   (and symmetric with NB)
  L3  C1 & NB => no a in A with N(a) = {c}, c in B         (and symmetric with NA)
  L4  C1 & NA & noiso & (no A-leaf on B) : if N_B(a) = {c} then N_A(a) = A-a, N_A(y) = {a} (y != a), N_A(c) = {a}
  L5  C1 & NA & NB & noiso : if some a has |N_B(a)| = 1 (or some b has |N_A(b)| = 1) then s = t = 3
  THM C1 & NA & NB & noiso => H = K_{A,B}  if (s,t) != (3,3);  H isomorphic to K_{3,3} if (s,t) = (3,3)
usage: verify_lemmas.py s t chunk_bits chunk_index [L0]"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); doL0 = len(sys.argv) > 5
n = s + t; full = (1 << n) - 1
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; Bmask = full & ~Amask
bit = lambda c: sum(1 << v for v in c)
pc = lambda x: bin(x).count('1')
minPD = [(1 << a) | (1 << b) for a in A for b in B] + [bit(c) for c in itertools.combinations(A, s - 1)] + [bit(c) for c in itertools.combinations(B, t - 1)]
NAs = [bit(c) for c in itertools.combinations(A, s - 2)]; NBs = [bit(c) for c in itertools.combinations(B, t - 2)]
Kn, Kadj = pdlib.kst_adj(s, t)
cnt = {k: [0, 0] for k in ['L0', 'L1', 'L2', 'L2sym', 'L3', 'L3sym', 'L4', 'L5', 'THM']}  # [instances, failures]
fails = []
def rec(k, ok, info=None):
    cnt[k][0] += 1
    if not ok:
        cnt[k][1] += 1
        if len(fails) < 10: fails.append((k, info))
def is_k33_iso(adj):
    # 3-regular bipartite on 6 vertices <=> K_{3,3}
    if any(pc(adj[v]) != 3 for v in range(n)): return False
    side = {0: 0}; st = [0]
    while st:
        x = st.pop()
        for y in range(n):
            if adj[x] >> y & 1:
                if y not in side: side[y] = 1 - side[x]; st.append(y)
                elif side[y] == side[x]: return False
    return len(side) == n
lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            u, v = E[k]; adj[u] |= 1 << v; adj[v] |= 1 << u
    noiso = all(adj)
    if doL0:
        forts = pdlib.all_forts(n, adj)
        for S in range(1 << n):
            NS = pdlib.closed_nbhd(n, adj, S)
            rec('L0', pdlib.is_pd(n, adj, S) == (not any(F & NS == 0 for F in forts)), (pdlib.edges_of(n, adj), S))
    C1 = all(pdlib.is_pd(n, adj, S) for S in minPD)
    if not C1: continue
    NA = not any(pdlib.is_pd(n, adj, S) for S in NAs)
    NB = not any(pdlib.is_pd(n, adj, S) for S in NBs)
    # L1
    for F in pdlib.all_forts(n, adj):
        NF = pdlib.closed_nbhd(n, adj, F)
        ok = (NF & Amask == Amask and pc(NF & Bmask) >= 2) or (NF & Bmask == Bmask and pc(NF & Amask) >= 2)
        rec('L1', ok, (pdlib.edges_of(n, adj), F))
    beta = {a: adj[a] & Bmask for a in A}; alpha = {b: adj[b] & Amask for b in B}
    if NA and noiso:
        rec('L2', all(beta[a] for a in A), pdlib.edges_of(n, adj))
    if NB and noiso:
        rec('L2sym', all(alpha[b] for b in B), pdlib.edges_of(n, adj))
    if NB:
        rec('L3', not any(adj[a] & Amask == 0 and pc(beta[a]) == 1 for a in A), pdlib.edges_of(n, adj))
    if NA:
        rec('L3sym', not any(adj[b] & Bmask == 0 and pc(alpha[b]) == 1 for b in B), pdlib.edges_of(n, adj))
    noAleaf = not any(adj[a] & Amask == 0 and pc(beta[a]) == 1 for a in A)
    if NA and noiso and noAleaf:
        for a in A:
            if pc(beta[a]) == 1:
                c = beta[a].bit_length() - 1
                ok = (adj[a] & Amask == Amask & ~(1 << a)) and all(adj[y] & Amask == 1 << a for y in A if y != a) and alpha[c] == 1 << a
                rec('L4', ok, pdlib.edges_of(n, adj))
    if NA and NB and noiso:
        if any(pc(beta[a]) == 1 for a in A) or any(pc(alpha[b]) == 1 for b in B):
            rec('L5', s == 3 and t == 3, pdlib.edges_of(n, adj))
        if (s, t) == (3, 3):
            rec('THM', is_k33_iso(adj), pdlib.edges_of(n, adj))
        else:
            rec('THM', adj == Kadj, pdlib.edges_of(n, adj))
print('s t chunk', s, t, cb, ci, 'counts [instances, failures]', cnt, 'fails', fails)
