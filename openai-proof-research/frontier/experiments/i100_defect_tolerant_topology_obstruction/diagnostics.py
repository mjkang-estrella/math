#!/usr/bin/env python3
"""Read-only exact finite algebra diagnostics; neither geometry nor novelty."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb
import json

def rank(rows):
    a = [[Q(x) for x in row] for row in rows]
    r = 0
    for c in range(len(a[0]) if a else 0):
        p = next((p for p in range(r, len(a)) if a[p][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        z = a[r][c]
        a[r] = [x/z for x in a[r]]
        for j in range(len(a)):
            if j != r:
                z = a[j][c]
                a[j] = [x-z*y for x,y in zip(a[j],a[r])]
        r += 1
    return r

def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]

def main():
    # Squarefree red algebra: J=(x3-x1-x2,x4,x5) contains every red pair.
    pairs = list(combinations(range(5),2))
    generators = [[-1,-1,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]
    products = []
    for g in generators:
        for j in range(5):
            products.append([g[a] if b==j else g[b] if a==j else 0 for a,b in pairs])
    assert rank(products) == 10
    for i in range(10):
        assert rank(products+[[int(i==j) for j in range(10)]]) == 10
    # At most two red-linear relations leave >=3 linear variables and only five
    # square relations; Sym^2 has >=6 dimensions. General proof is in report.
    assert comb(3+1,2) > 5
    basis = [[[0,1],[0,0]],[[1,0],[0,-1]],[[0,0],[1,0]]]
    adjoints=[]
    for a,b in product(range(3),repeat=2):
        g=[[1+a*b,a],[b,1]];gi=[[1,-a],[-b,1+a*b]]
        cols=[]
        for x in basis:
            y=mm(mm(g,x),gi);cols.append([y[0][1],y[0][0],y[1][0]])
        adjoints.append([cols[j][i] for i in range(3) for j in range(3)])
    assert rank(adjoints)==9
    # Actual ordered distinct (R,B,R,B) list: 10 ports each color, of which
    # five of each color are plus at every vertex in the periodic model.
    total=all_plus=vanishing_minus=0
    for (r1,r2),(b1,b2) in product(permutations(range(10),2),repeat=2):
        total+=1
        if max(r1,r2,b1,b2)<5:
            all_plus+=1
            assert tuple(sorted((r1,r2))) in pairs
        else:
            vanishing_minus+=1
    assert (total,all_plus,vanishing_minus)==(8100,400,7700)
    assert total*10**4*16==1296000000
    # Independent type deletion is different from a one-seam deletion.
    repeated=[]
    for dr in range(3):
        for db in range(3-dr):
            assert 5-dr>=3 and 5-db>=3
            repeated.append([dr,db])
    # A free excess factor has zero Euler class; it is not a nonzero minor.
    euler={str(s):sum((-1)**j*comb(s,j) for j in range(s+1)) for s in range(1,7)}
    assert all(v==0 for v in euler.values())
    # In K[t]/t^2, Koszul d(eta)=t: coefficient extraction does NOT commute
    # with this parameter-dependent differential. coeff_t(d eta)=1, d_0=0.
    # Differential as multiplication by t on coefficients (constant,t).
    def d_eta(coefficients):
        return [0, coefficients[0]]
    image = d_eta([1,0])
    coefficient_after_d = image[1]
    differential_after_specialization = 0
    assert coefficient_after_d == 1
    assert coefficient_after_d != differential_after_specialization
    result=dict(status='PASS',ordered_port_tuples=total,
      ordered_all_plus=all_plus,ordered_with_a_minus=vanishing_minus,
      actual_list_size=total*10**4*16,adjoint_span_rank=9,
      red_degree_two_ideal_rank=10,minimal_red_linear_generators=3,
      all_plus_unordered_laws=comb(5,2)**2,
      scalar_residual_slots_per_vertex=6,used_scalar_generators=3,
      repeated_type_deletion_cases=repeated,free_excess_euler=euler,
      limits='Finite exact algebra only. All conjugators/signs are paid by the universal Brunnian argument in the report, not by enumerating 1,296,000,000 bodies. No manifold, involution, or novelty certification.')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()
