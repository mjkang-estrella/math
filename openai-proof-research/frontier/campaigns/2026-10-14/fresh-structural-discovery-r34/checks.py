#!/usr/bin/env python3
"""MIT. Exact diagnostic examples; not a proof of a language-height bound."""
from fractions import Fraction
from itertools import product
import json

def clock(n, sets):
    ins, outs = sets[:2], sets[2:]
    edges = [set() for _ in range(n)]
    for i,j in product(range(2), repeat=2):
        for a,b in product(ins[i], outs[j]):
            edges[(a+b)%n].add((i,j))
    diag={(0,0),(1,1)}
    valid=all(e <= diag or (len(e)==1 and next(iter(e))[0]!=next(iter(e))[1]) for e in edges)
    good={z for z,e in enumerate(edges) if e==diag}
    return valid, good, edges

def main():
    results=[]
    for n in range(1,5):
        subsets=[{i for i in range(n) if mask>>i&1} for mask in range(1,1<<n)]
        valid_count=0
        for sets in product(subsets, repeat=4):
            valid,good,edges=clock(n,sets)
            if not valid or not good:
                continue
            valid_count+=1
            bad=set(range(n))-good
            assert len(bad)**2 >= 4*len(good)
            cross=[{z for z,e in enumerate(edges) if (i,j) in e} for i,j in [(0,1),(1,0)]]
            assert cross[0] and cross[1] and not cross[0]&cross[1]
            assert all(c <= bad for c in cross)
        results.append({'cyclic_order':n,'active_two_tag_clocks_with_good_total':valid_count})
    valid,good,edges=clock(3,({0},{1},{0},{2}))
    assert valid and good=={0}
    assert edges[2]=={(0,1)} and edges[1]=={(1,0)}
    # The singleton edge can certify only the prefix tag's input state.
    X={0:0,1:1}
    allowed_inputs={X[i] for i,j in edges[2]}
    assert allowed_inputs=={0} and 1 not in allowed_inputs
    # Control: if the unique true witness promise is deleted, uniqueness
    # alone can select the wrong candidate.
    witnesses={0:False,1:True,2:False}
    selected=[p for p,v in witnesses.items() if v]
    assert selected==[1] and selected[0]!=0
    lll=[]
    for a,q,k in [(2,2,2),(3,2,3),(2,4,2)]:
        r=1
        while True:
            length=k*r
            bound=k*q*(1+length*(a-1)+length*(length-1)//2*(a-1)**2)
            failure=(1-Fraction(1,q**(a-1)))**r
            if 4*bound*failure<=1:
                break
            r+=1
        lll.append({'a':a,'q':q,'blocks':k,'block_length':r,
                    'four_D_failure_numerator':(4*bound*failure).numerator,
                    'four_D_failure_denominator':(4*bound*failure).denominator})
    print(json.dumps({'finite_clock_exhaustion':results,
                      'sharp_three_element_clock':{'good':[0],'off_diagonal_totals':[1,2]},
                      'missing_true_witness_control':'unique false witness selected',
                      'simultaneous_grid_sufficient_bounds':lll,
                      'scope':'Finite diagnostics only; no instantiated enormous source clock or height-two proof.'},sort_keys=True,indent=2))

if __name__=='__main__': main()
