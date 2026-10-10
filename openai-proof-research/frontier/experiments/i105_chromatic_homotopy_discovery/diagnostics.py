"""Finite exact diagnostics only; not a proof checker for spectral assertions."""
from collections import Counter
from itertools import product


def run():
    def shift(c, k):
        return Counter({d + k: m for d, m in c.items()})
    ga1 = Counter({-2: 1})
    ga2 = shift(shift(ga1, -1) + Counter({-3: 1, -4: 1}), -1)
    assert ga2 == {-4: 2, -5: 1}
    gw = ga2 + shift(ga2, -1)
    gu = shift(ga1, -3) + shift(ga1, -4)
    possible = sorted(set(gu) & set(shift(gw, 1)))
    assert possible == [-5]  # Its actual map is killed separately in the proof.
    gf = gw + gu
    assert gf == {-4: 2, -5: 4, -6: 2}
    boundary = shift(gf, 1)
    ranks = {d: boundary[d] for d in (-5, -6, -8, -9)}
    assert ranks == {-5: 2, -6: 0, -8: 0, -9: 0}
    # Exterior basis on generators t,z,d of degrees -1,-1,-3.
    def mul(a, b):
        if a & b:
            return (0, 0)
        inversions = sum(bool(a & (1 << i)) and bool(b & (1 << j))
                         for i in range(3) for j in range(3) if i > j)
        return (-1 if inversions % 2 else 1, a | b)
    def scale_mul(term, b):
        s, mask = term
        q, mask2 = mul(mask, b)
        return (s * q, mask2 if s * q else 0)
    for a,b,c in product(range(8), repeat=3):
        lhs = scale_mul(mul(a,b),c)
        s,mask = mul(b,c)
        q,mask2 = mul(a,mask)
        rhs = (s*q,mask2 if s*q else 0)
        assert lhs == rhs
    images = (2,4,7)  # z,d,tzd; the last has arbitrary scalar coefficient.
    for a in images:
        assert mul(a,a)[0] == 0
    for a,b in product(images,repeat=2):
        s,m = mul(a,b); q,n = mul(b,a)
        assert s == -q and (not s or m == n)
    assert mul(1,6) == (1,7)
    def odd_height_one_nonzero(p, degree):
        if degree in (0,-1):return True
        return degree % 2 != 0 and ((degree+1)//2) % (p-1) == 0
    for p in (5,7,11,13):
        assert not odd_height_one_nonzero(p,-2)
        assert not odd_height_one_nonzero(p,-3)
        for a in range(9):
            t=(p-1)*p**a; v=0
            while t % p == 0:v+=1;t//=p
            assert v == a
    return {'Gamma_A2':dict(ga2),'Gamma_F4':dict(gf),'boundary_ranks':ranks,
            'exterior_associativity_triples':512,'height_one_sample_primes':[5,7,11,13],
            'status':'Exact finite diagnostics; universal claims require the report proofs.'}

if __name__ == '__main__':
    import json
    print(json.dumps(run(),sort_keys=True))
