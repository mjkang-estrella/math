#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Exact finite identities only; cannot validate infinite-volume proof bridges."""
from fractions import Fraction as Q
import json

def check():
    rows=[]
    for weights in [(2,13,3,17,65),(1,20,2,30,47),(7,11,13,17,52)]:
        masses=[Q(x,100) for x in weights]
        ao,bo,ac,bc,rest=masses
        delta=min(ao,ac)/3
        density=[1-delta/ao,1+delta/bo,1-delta/ac,1+delta/bc, Q(1)]
        assert sum(p*l for p,l in zip(masses,density))==1
        assert sum(p*l*l for p,l in zip(masses,density))==1+delta**2*(1/ao+1/bo+1/ac+1/bc)
        assert ao*(delta/ao)+ac*(delta/ac)==2*delta
        for high in (bo,bc):
            assert (delta/high)/(1+delta/high)==delta/(high+delta)
        # Reversibility inside each status: pi(i)K(i,j)=pi(j)K(j,i).
        for low,high in [(ao,bo),(ac,bc)]:
            total=low+high
            assert low*high/total==high*low/total
        rows.append({'case':'two-status-density-posterior-reversibility','masses':weights})
    # Exact diagonal crossing inventory. h=-1/2, u=x-y.
    for m in range(2,21):
        crossings=sorted({Q(2*k)+d for k in range(-m,m+1) for d in (Q(-1,2),Q(1,2))})
        assert crossings==[Q(-2*m)-Q(1,2)+j for j in range(4*m+2)]
        assert crossings[-1]-crossings[0]>4*m
    rows.append({'case':'diagonal-crossing-parity','m_min':2,'m_max':20})
    # Discrete summation-by-parts identity, for arbitrary usable patterns.
    for n in range(1,9):
        f=[Q(1,(j+2)*(j+3)) for j in range(1,n+1)]
        for mask in range(1<<n):
            bits=[(mask>>j)&1 for j in range(n)]
            partial=[];a=0
            for bit in bits:a+=bit;partial.append(a)
            assert sum(bit*fj for bit,fj in zip(bits,f))==partial[-1]*f[-1]+sum(partial[j]*(f[j]-f[j+1]) for j in range(n-1))
    rows.append({'case':'Abel-identity','all_binary_patterns_through_length':8,'limit_divergence_checked':False})
    # The uncapped-output premise is essential for the claimed fixed cap gain.
    low,high,K=Q(2),Q(9),Q(10)
    assert min(high,K)-min(low,K)==high-low
    K=Q(1)
    assert min(high,K)-min(low,K)<high-low
    rows.append({'case':'cap-gain-positive-and-negative-premise-control'})
    # Negative control: forgetting second status gives the wrong second moment.
    assert sum(p*l*l for p,l in zip(masses,density)) != 1+delta**2*(1/ao+1/bo)
    rows.append({'case':'omitted-status-negative-control'})
    return {'status':'PASS_FINITE_IDENTITIES_ONLY','full_theorem_verified':False,
            'structural_bridges_verified':False,'cases':rows}

if __name__=='__main__':print(json.dumps(check(),indent=2))
