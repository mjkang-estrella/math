# Exact certificate: two affinely inequivalent 25-element extreme subsets of Z_71.
import json, cmath, sys
p = 71
c1 = [0, 1, -1, 1, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, -1, 0, 0, 1, 1, 0, 0, -1, 1, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0]
c2 = [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, 0, -1, 1, 1, 0, 0, -1, 0, 0, 1, -1, -1, -1, 1, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0]
c3 = [0, 1, 0, -1, -1, 1, 0, 1, 0, -1, 0, 1, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 1, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
res = {}
for name, c in (('c1', c1), ('c2', c2), ('c3', c3)):
    assert len(c) == p and set(c) <= {-1, 0, 1}
    E = [x for x in range(p) if c[x]]
    A = [sum(c[x]*c[(x+g) % p] for x in range(p)) for g in range(p)]
    assert A[0] == 25 and all(a == 0 for a in A[1:])
    # |mu-hat(k)|^2 = sum_g A(g) e^{2 pi i k g/p} = 25 exactly; numerical spot check:
    mx = max(abs(abs(sum(c[x]*cmath.exp(-2j*cmath.pi*k*x/p) for x in range(p)))-5) for k in range(p))
    res[name] = {'support': E, 'size': len(E), 'autocorrelation_ok': True, 'max_dev_|muhat|_from_5': mx,
                 'norm_mu': sum(abs(v) for v in c)}
def canon(S):
    return min(tuple(sorted((a*x+b) % p for x in S)) for a in range(1, p) for b in range(p))
cs = {k: canon(v['support']) for k, v in res.items()}
res['pairwise_affine_equivalent'] = {f'{a}-{b}': cs[a] == cs[b] for a in cs for b in cs if a < b}
res['primality_71'] = all(71 % d for d in range(2, 71))
print(json.dumps(res, indent=1))
