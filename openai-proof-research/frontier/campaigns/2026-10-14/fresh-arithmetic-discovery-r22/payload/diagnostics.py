#!/usr/bin/env python3
"""Finite supporting checks, not a proof of robust Ostmann.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
"""
from fractions import Fraction
from itertools import combinations
import json

def require(condition,message):
    if not condition: raise ValueError(message)

def subsets(items):
    for size in range(len(items)+1):
        for s in combinations(items,size): yield set(s)

def prime(n):
    return n>=2 and all(n%d for d in range(2,int(n**.5)+1))

def finite_injection(A,B,P,x):
    D=max(A)-min(A)
    S={a+b for a in A for b in B}
    isolated={p for p in P if p<=x-D and not any(0<abs(p-q)<=2*D for q in P)}
    images={}
    for p in sorted(isolated&S):
        a,b=next((a,b) for a in sorted(A) for b in sorted(B) if a+b==p)
        other=next(t for t in sorted(A) if t!=a)
        q=other+b
        require(0<=q<=x and q in S-P,'bad nonprime image')
        require(q not in images,'noninjective images')
        images[q]=p
    errors={v for v in S^P if 0<=v<=x}
    require(len(errors)>=len(isolated),'isolation bound failed')
    return len(isolated),len(images)

def main():
    cases=images=0
    # Exhaustive arbitrary marked sets; points through x+2D are included.
    for A in subsets(list(range(4))):
        if len(A)<2:continue
        for B in subsets(list(range(5))):
            for P in subsets(list(range(9))):
                # P is the entire finite marked set, hence isolation is global.
                _,i=finite_injection(A,B,P,8);cases+=1;images+=i
    primes={n for n in range(101) if prime(n)}
    for A in ({0,1},{0,2},{1,4},{0,3,7},{2,4,8}):
        for B in (set(),{0},{0,1},primes,{p-2 for p in primes if p>=2},set(range(25))):
            finite_injection(A,B,primes,80)
    mass=[]
    for m in (2,3,8,32):
        counts={n:sum(a+b==n for a in range(m) for b in range(m)) for n in range(2*m-1)}
        require(len(counts)==2*m-1 and sum(counts.values())==m*m,'pair mass')
        mass.append({'m':m,'distinct_bad_labels':len(counts),'bad_pairs':sum(counts.values()),'ambient_X':m**3})
    weights=[]
    for n in (16,256,4096):
        size=int(n**.5);height=Fraction(n,size)
        require(Fraction(size,n)*height==1,'weight mean')
        weights.append({'points':n,'exceptional_points':size,'exception_fraction':str(Fraction(size,n)),'height':str(height),'normalized_exceptional_mass':'1'})
    return {'status':'PASS','arbitrary_marked_set_cases':cases,'covered_isolated_cases_total':images,'prime_edge_cases':30,'pair_mass_examples':mass,'weight_concentration_models':weights,'limits':'Finite combinatorial checks and generic mass models only; no prime counterexample, cleaning theorem, asymptotic verification or full-target proof.'}

if __name__=='__main__':print(json.dumps(main(),indent=2))
