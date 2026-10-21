"""Bounded exact diagnostics for a proposed q-Hikita multiport extension.
Not a test of stipulated source truth or an exhaustive graph search.
"""
from fractions import Fraction as F
from itertools import permutations, combinations
from collections import defaultdict
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def qnum(n,q):
    if q==1:return F(n)
    return (q**n-1)/(q-1)
def elementary(xs):
    e=[F(1)]+[F(0)]*len(xs)
    for x in xs:
        for j in range(len(xs),0,-1):e[j]+=x*e[j-1]
    return e
def transitions(state,op,kind,xs,q):
    if op=='D':
        if not state:return []
        wt=F(1) if kind=='color' else elementary(xs)[state[0]]/elementary(xs)[state[0]-1]
        return [(state[1:],wt)]
    N=len(xs)
    if kind=='color':return [(state+(c,),xs[c-1]*q**sum(a<c for a in state)) for c in range(1,N+1) if c not in state]
    red=lambda i:i<=0 or i in state
    W=[i for i in range(1,N+2) if not red(i) and red(i-1)]
    R=[i for i in range(1,N+2) if red(i) and not red(i-1)]
    out=[]
    for y in W:
        if y>N:continue
        wt=qnum(y,q)
        for b in R:wt*=qnum(y-b,q)
        for a in W:
            if a!=y:wt/=qnum(y-a,q)
        out.append((state+(y,),wt))
    return out
def trace(word,k,kind,xs,q):
    ans=F(0)
    for start in permutations(range(1,len(xs)+1),k):
        dp={start:F(1)}
        for op in word:
            nxt=defaultdict(F)
            for s,w in dp.items():
                for t,z in transitions(s,op,kind,xs,q):nxt[t]+=w*z
            dp=nxt
        ans+=dp.get(start,0)
    return ans
def run():
    rows=[]
    for N in (2,3,4):
        xs=tuple(map(F,(2,3,5,7)[:N]))
        for q in (F(1),F(2),F(1,2)):
            for k in range(1,N):
                for n in range(2,9):
                    word='MD'*n
                    a=trace(word,k,'color',xs,q);b=trace(word,k,'tableau',xs,q)
                    rows.append(dict(N=N,q=str(q),k=k,n=n,word=word,color=str(a),tableau=str(b),equal=a==b))
    (ROOT/'notes/graded-boundary-diagnostics.json').write_text(json.dumps(rows,indent=2)+'\n')
    bad=[r for r in rows if not r['equal']]
    print(json.dumps(dict(tests=len(rows),mismatches=len(bad),first_mismatches=bad[:8]),indent=2))
if __name__=='__main__':run()
