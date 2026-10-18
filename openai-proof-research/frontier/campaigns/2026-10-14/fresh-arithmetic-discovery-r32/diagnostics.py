#!/usr/bin/env python3
"""MIT. Exact polynomial matrix diagnostics; not a formal proof certificate."""
import json

def clean(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p)
def add(p,q):return clean(tuple((p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))))
def mul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return clean(r)
def mat(a):return [[x if isinstance(x,tuple) else (x,) for x in row] for row in a]
def mm(a,b):
    out=[]
    for row in a:
        rr=[]
        for col in zip(*b):
            v=(0,)
            for x,y in zip(row,col):v=add(v,mul(x,y))
            rr.append(v)
        out.append(rr)
    return out
def mod2(a):return [[clean(tuple(x%2 for x in p)) for p in row] for row in a]

S=mat([[1,0,0,0],[0,-1,0,0],[0,1,1,0],[-1,0,0,-1]])
T=mat([[1,0,0,0],[0,1,0,0],[-1,-1,-1,0],[-1,(0,-1),0,-1]])
I=mat([[int(i==j) for j in range(4)] for i in range(4)])
assert mm(S,S)==I and mm(T,T)==I and mm(S,T)==mm(T,S)
V=mat([[1,0,0,0],[0,1,0,0],[1,1,2,0],[1,(0,1),0,2]])
Ds=mat([[int(i==j)*[1,-1,1,-1][i] for j in range(4)] for i in range(4)])
Dt=mat([[int(i==j)*[1,1,-1,-1][i] for j in range(4)] for i in range(4)])
assert mm(Ds,V)==mm(V,S) and mm(Dt,V)==mm(V,T)
B=mat([[0,1],[1,0]]);C=mat([[1,1],[1,(0,1)]])
J=mat([[1,(0,1)],[1,1]])
assert mm(B,C)==J
# For D=[[x,y],[z,w]], DJ=JD iff w=x and y=a*z; hence dimension2.
# Basis of its centralizer: I_2 and [[0,a],[1,0]].
Q=mat([[0,(0,1)],[1,0]])
assert mod2(mm(Q,J))==mod2(mm(J,Q))
det=add(mul(J[0][0],J[1][1]),mul((-1,),mul(J[0][1],J[1][0])))
assert tuple(x%2 for x in det)==(1,1)
print(json.dumps({'status':'PASS','identities':['commuting integral involutions over Z[a]','four-character basis intertwines both generators','intrinsic reduced matrix determinant 1+a','two-dimensional nonscalar centralizer formula'],'limit':'Symbolic algebra checks support the direct proof; no classification or formal theorem certification.'},indent=2))
