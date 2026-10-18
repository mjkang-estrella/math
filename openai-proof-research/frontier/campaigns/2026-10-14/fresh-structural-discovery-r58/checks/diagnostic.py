#!/usr/bin/env python3
"""MIT. Exact finite diagnostics; not a proof of the provisional algorithmic question."""
from itertools import combinations
from fractions import Fraction
import json

def ed(x,y):
    row=list(range(len(y)+1))
    for i,a in enumerate(x,1):
        nxt=[i]
        for j,b in enumerate(y,1):
            nxt.append(min(nxt[-1]+1,row[j]+1,row[j-1]+(a!=b)))
        row=nxt
    return row[-1]

def main():
    pairs=0;repetitions=0;strict=0;example=None
    for n in (2,4,6,8,10):
        x=list(range(n));h=n//2
        for k in range(1,n):
            for subset in combinations(range(n),k):
                y=x[h:]+x[:h]
                for j in subset:y[j]=n+j
                ced=min(ed(x,y[j:]+y[:j]) for j in range(n))
                assert ced==k
                pairs+=1
                for t in (1,2,3,4):
                    e=ed(x*t,y*t);assert e>=max(t*k,n)
                    repetitions+=1
                    if e>t*k:
                        strict+=1
                        if n==10 and k==1 and t==2 and example is None:
                            example={'n':n,'k':k,'t':t,'x':x,'y':y,'ced':ced,'ordinary_repetition_distance':e}
    eps=Fraction(1,100);R=100
    true=[[R,R+1],[R-1,R]];approx=[[R+1,R+1],[R-1,R]]
    for s in range(2):
        for j in range(2):
            e=1+R+j
            assert true[s][j]==ed([0],[0]*(e-s))
            assert true[s][j]<=approx[s][j]<=(1+eps)*true[s][j]
    assert true[0][0]+true[1][1]==true[0][1]+true[1][0]
    assert approx[0][0]+approx[1][1]>approx[0][1]+approx[1][0]
    return {'status':'PASS','replacement_pairs':pairs,'repetition_instances':repetitions,'strictly_above_t_times_ced':strict,'example':example,'monge_true':true,'monge_approx':approx,'monge_accuracy':'1/100','scope':'Finite exact replay of two specified route obstructions; no general algorithm, theorem novelty, or independent review.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
