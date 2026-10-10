"""Exact finite diagnostics only, not universal operator-proof certification.

Offline and read-only. Python -B is recommended; bytecode is disabled here too.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import product
from math import comb
import json

def run():
    counts = {}
    count = 0
    # Exact diagonal finite-support states, including every boundary ladder term.
    for n, width in [(1, 9), (2, 4), (3, 2)]:
        points = list(product(range(width), repeat=n))
        for r in [F(1, 5), F(1), F(7, 3)]:
            for seed in range(1, 8):
                weights = {p: F(1 + ((sum((j+2)*x for j,x in enumerate(p))+seed)**2 % 17)) for p in points}
                z = sum(weights.values()); probs = {p: v/z for p,v in weights.items()}
                tau = lambda p: (r+1)**(-n)*(r/(r+1))**sum(p)
                overlap = sum(v*tau(p) for p,v in probs.items())
                norm2 = sum(v*v for v in probs.values()) - overlap**2*(2*r+1)**n
                residual2 = F(0)
                for j in range(n):
                    targets = set(points)
                    for p in points:
                        q = list(p); q[j] += 1; targets.add(tuple(q))
                    for q in targets:
                        if not q[j]: continue
                        prev = list(q); prev[j] -= 1
                        residual2 += q[j]*((r+1)*probs.get(q,0)-r*probs.get(tuple(prev),0))**2
                assert norm2 >= 0
                assert (2*r+1)*norm2 <= 2*residual2
                c = overlap*(2*r+1)**n
                assert 0 <= c <= ((2*r+1)/(r+1))**n
                count += 1
    counts['balance_finite_diagonal_states'] = count
    count = 0
    # Finite classical states test the actual reference shift in Q114.
    for modes in range(1, 5):
        for cutoff in range(0, 9):
            weights = [[F(1+(x+2)*(j+3)%13) for j in range(3)] for x in range(cutoff+4)]
            total = sum(map(sum, weights)); w = [[v/total for v in row] for row in weights]
            marginal = [sum(row) for row in w]
            effect = [F(1, 3**modes*2**x) for x in range(len(w))]
            probability = sum(a*b for a,b in zip(effect,marginal))
            ref = [sum(effect[x]*w[x][j] for x in range(len(w)))/probability for j in range(3)]
            filtered_error = sum(effect[x]*abs(w[x][j]-marginal[x]*ref[j]) for x in range(len(w)) for j in range(3))
            compressed_error = sum(abs(w[x][j]-marginal[x]*ref[j]) for x in range(cutoff+1) for j in range(3))
            assert compressed_error <= 3**modes*2**cutoff*filtered_error
            count += 1
    counts['inverse_filter_reference_shift_cases'] = count
    count = 0
    for n in range(1, 10):
        for k in range(30):
            assert comb(k+n,n) <= (k+1)**n
            count += 1
    counts['simplex_rank_cases'] = count
    for k in range(64, 2049):
        variance = (F(6)+5*k+2)/4
        assert variance == F(5*k,4)+2
        assert variance/(F(k,4)+1)**2 <= F(20,k)+F(32,k*k)
        assert F(12,k)+F(16,k*k) < F(1,2)
    counts['rare_fock_tail_budgets'] = 2049-64
    count = 0
    max_depth = 0
    for n in range(1, 9):
        J = 8*4096*(n+1)**3
        for k in range(1, 65):
            epsilon = F(1,2**k); depth = 1
            while 18*J*F(3,4)**depth > epsilon/4: depth += 1
            assert 18*J*F(3,4)**depth <= epsilon/4
            assert 18*J*F(3,4)**(depth-1) > epsilon/4
            # Conservative explicit linear budget; no floating logarithm used.
            assert depth <= 8*(k+n+32)
            max_depth = max(max_depth, depth); count += 1
    counts['synthesis_precision_budgets'] = count
    counts['maximum_tested_synthesis_depth'] = max_depth
    return {'status':'PASS', 'scope':'Finite exact rational diagnostics; no universal-proof or novelty certification', 'counts':counts}

if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
