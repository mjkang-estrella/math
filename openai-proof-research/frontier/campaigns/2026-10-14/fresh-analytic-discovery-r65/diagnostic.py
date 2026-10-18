#!/usr/bin/env python3
# Copyright2026 Myeongjin Kang. MIT.
"""Finite algebra controls only, not bounds for infinite maximal operators."""
from fractions import Fraction as F
from itertools import product
import json

def need(x,message):
    if not x:raise ValueError(message)

def main():
    # Exact parabolic-coordinate identities; each is polynomial, proof in flow-route.
    grid=[F(-1),F(-1,2),F(0),F(1,2),F(1)]
    cases=0
    for X,Y,s in product(grid,repeat=3):
        Q=Y-X*X/2
        need(Y-s*X-(X-s)**2/2==Q-s*s/2,'frozen coordinate')
        need(Y-s*X+s*s/2-(X-s)**2/2==Q,'flow coordinate')
        cases+=1
    need((F(1,2)**3-F(1,4)**3)/12==F(7,768),'curvature integral lower bound')
    need(1-F(1,2)**2/6>=F(1,2),'sine Taylor lower factor')
    # Orthogonal coordinate signs: bandwise norm1 and maximum K, not sqrt(K).
    rows=[]
    for K in range(1,7):
        xs=list(product((-1,1),repeat=K));N=len(xs)
        for i in range(K):
            for j in range(K):
                need(sum(x[i]*x[j] for x in xs)==(N if i==j else 0),'orthogonality')
        input_sq=F(sum(sum(x)**2 for x in xs),N)
        output_sq=F(sum(max(abs(sum(s*t for s,t in zip(sign,x))) for sign in xs)**2 for x in xs),N)
        need(input_sq==K and output_sq==K*K,'selected maximum')
        rows.append({'K':K,'operators':N,'input_norm_squared':K,'maximal_norm_squared':K*K})
    need(rows[-1]['maximal_norm_squared']>rows[-1]['input_norm_squared'],'reject dimension-free constant1 transfer')
    print(json.dumps({'status':'PASS_FINITE_ALGEBRA_ONLY','parabolic_coordinate_cases':cases,'annular_lower_bound':'7/768','signed_orthogonal_examples':rows,'full_083_maximal_theorem_proved':False},indent=2))
if __name__=='__main__':main()
