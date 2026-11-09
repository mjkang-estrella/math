"""List all permutations of [n] with RLMv = R and EXCv = E (and their cycle types, inversion parities), to certify the
coefficient of x_R y_E in the Alexandersson-Kebede signed sum for each k.  usage: signed_rlm_cert.py n R E
(R, E comma-separated)"""
import sys, itertools, json
n = int(sys.argv[1]); R = sorted(map(int, sys.argv[2].split(','))); E = sorted(map(int, sys.argv[3].split(',')))
rows = []
for p in itertools.permutations(range(1, n + 1)):
    exc = sorted(p[i] for i in range(n) if p[i] > i + 1)
    if exc != E: continue
    rlm = []; cur = n + 1
    for i in range(n - 1, -1, -1):
        if p[i] < cur: rlm.append(p[i]); cur = p[i]
    if sorted(rlm) != R: continue
    seen = [False] * (n + 1); cyc = []
    for s in range(1, n + 1):
        if not seen[s]:
            L = 0; x = s
            while not seen[x]: seen[x] = True; x = p[x - 1]; L += 1
            cyc.append(L)
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
    rows.append(dict(perm=''.join(map(str, p)), cycle_type=sorted(cyc, reverse=True), inv=inv, sign=-1 if inv % 2 else 1))
by_k = {k: sum(r['sign'] for r in rows if min(r['cycle_type']) >= k) for k in range(1, n + 1)}
print(json.dumps(dict(n=n, R=R, E=E, total_perms=len(rows), coefficient_by_k=by_k,
                      contributors_k3=[r for r in rows if min(r['cycle_type']) >= 3]), indent=0))
