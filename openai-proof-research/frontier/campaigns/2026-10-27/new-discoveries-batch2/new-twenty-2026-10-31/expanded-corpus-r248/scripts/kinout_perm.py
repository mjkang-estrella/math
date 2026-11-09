"""335271, a=0 path-tree case as a permutation problem.
If both spanning trees (out-pairs T_out, in-pairs T_in) are paths, then in path coordinates the closed successor
permutation is F_{S,T} = tau * B_S^{-1} * mu * B_T on {0..k-1}, B_T = cycle (0 1 ... T-1) (B_1 = id),
tau in S_k arbitrary, mu in S_k fixing 0. Paired condition: for every S exactly one T with F_{S,T} a k-cycle,
and S -> T injective. Count (tau, mu) solutions for given k.
usage: kinout_perm.py k OUTNAME"""
import sys, itertools, json, os, time
k = int(sys.argv[1])
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
outp = f'{D}/outputs/kinout/{sys.argv[2]}.json'
if os.path.exists(outp):
    raise SystemExit('exists')
t0 = time.time()
perms = list(itertools.permutations(range(k)))
idx = {p: i for i, p in enumerate(perms)}


def comp(a, b):  # (a*b)(x) = a(b(x))
    return tuple(a[b[x]] for x in range(k))


def kcycle(p):
    x = p[0]
    L = 1
    while x != 0:
        x = p[x]
        L += 1
    return L == k


B = []
for T in range(1, k + 1):
    b = list(range(k))
    for j in range(T - 1):
        b[j] = j + 1
    b[T - 1] = 0
    B.append(tuple(b))
Binv = [tuple(sorted(range(k), key=lambda x: b[x])) for b in B]
# row pattern: for g, the list of T (0-based index) with g*B_T a k-cycle
good = []
for g in perms:
    r = [T for T in range(k) if kcycle(comp(g, B[T]))]
    good.append(r[0] if len(r) == 1 else -1)
mus = [p for p in perms if p[0] == 0]
sol = 0
examples = []
for tau in perms:
    rows = [comp(tau, Binv[S]) for S in range(k)]
    for mu in mus:
        used = 0
        ok = True
        for S in range(k):
            T = good[idx[comp(rows[S], mu)]]
            if T < 0 or (used >> T) & 1:
                ok = False
                break
            used |= 1 << T
        if ok:
            sol += 1
            if len(examples) < 10:
                examples.append({'tau': tau, 'mu': mu})
res = {'k': k, 'pairs_tested': len(perms) * len(mus), 'solutions': sol, 'examples': examples, 'seconds': round(time.time() - t0, 1)}
open(outp, 'x').write(json.dumps(res) + '\n')
print(json.dumps(res)[:600])
