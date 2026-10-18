#!/usr/bin/env python3
"""MIT. Exact finite checks of examples; not an embedding theorem."""
import json, math
from fractions import Fraction

def ed(a,b):
    row=list(range(len(b)+1))
    for i,x in enumerate(a,1):
        nxt=[i]
        for j,y in enumerate(b,1):
            nxt.append(min(nxt[-1]+1,row[j]+1,row[j-1]+(x!=y)))
        row=nxt
    return row[-1]
def lcs(a,b):
    row=[0]*(len(b)+1)
    for x in a:
        nxt=[0]
        for j,y in enumerate(b,1):
            nxt.append(row[j-1]+1 if x==y else max(row[j],nxt[-1]))
        row=nxt
    return row[-1]
def binweights(n,k):
    return [math.comb(n,j)*(k-1)**(n-j) for j in range(n+1)]
def tv(a,b):
    return sum(abs((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0)) for i in range(max(len(a),len(b))))/2

def main():
    blocks=origins=0
    for L in range(2,8):
        for m in range(2,8):
            x=('0'*L+'1'*L)*m;y='1'+x[:-1]
            assert ed(x,y)==2
            ds=[ed(x[i:i+L],y[i:i+L]) for i in range(0,len(x),L)]
            rs=[L-lcs(x[i:i+L],y[i:i+L]) for i in range(0,len(x),L)]
            assert ds==rs==[1]*(2*m);blocks+=1
            for a in range(1,L):
                for i in range(a,len(x)-L+1,L):
                    assert abs(x[i:i+L].count('0')-y[i:i+L].count('0'))==1
                    origins+=1
    identities=0
    for k in range(2,6):
        for t in range(31):
            a=[Fraction(w,k**t) for w in binweights(t,k)]
            b=[Fraction(w,k**(t+1)) for w in binweights(t+1,k)]
            assert tv(a,b)==max(a)/k;identities+=1
    traces=[]
    for k in (2,3):
        last=None
        for N in (10,20,40,80):
            a=binweights(N,k);b=binweights(N+k,k);c=binweights(N-k,k)
            delta=0
            for i in range(N+k+1):
                for j in range(N+1):
                    aa=a[i]*a[j] if i<=N else 0
                    bb=b[i]*c[j] if j<=N-k else 0
                    delta+=abs(aa-bb)
            distance=Fraction(delta,2*k**(2*N))
            bound=2*max(Fraction(max(binweights(t,k)),k**t) for t in range(N-k,N+k))
            assert distance<=bound
            if last is not None: assert distance<last
            last=distance
            traces.append({'K':k,'N':N,'TV_exact':str(distance),'TV_decimal':float(distance),'telescoping_bound':float(bound)})
    return {'status':'PASS','fixed_block_pairs':blocks,'interior_offset_blocks':origins,'exact_binomial_shift_identities':identities,'trace_pairs':traces,'scope':'Finite diagnostics of specified repair obstructions only; not proof of the frozen target or of asymptotic decay.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
