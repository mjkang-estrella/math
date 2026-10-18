#!/usr/bin/env python3
"""MIT. Exact small matrices only; no asymptotic or contribution verification."""
from fractions import Fraction as F
from itertools import combinations
import json

def rank(a):
    a=[[F(x) for x in row] for row in a];n=len(a);m=len(a[0]) if n else 0;r=0
    for j in range(m):
        k=next((k for k in range(r,n) if a[k][j]),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r];z=a[r][j];a[r]=[x/z for x in a[r]]
        for k in range(r+1,n):
            z=a[k][j];a[k]=[x-z*y for x,y in zip(a[k],a[r])]
        r+=1
    return r

def inv(a):
    n=len(a);a=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        k=next((k for k in range(j,n) if a[k][j]),None)
        if k is None:return None
        a[j],a[k]=a[k],a[j];z=a[j][j];a[j]=[x/z for x in a[j]]
        for k in range(n):
            if k==j:continue
            z=a[k][j];a[k]=[x-z*y for x,y in zip(a[k],a[j])]
    return [row[n:] for row in a]

def mat(n,coords,mask):
    a=[[0]*n for _ in range(n)]
    for k,(i,j) in enumerate(coords):a[i][j]=a[j][i]=(mask>>k)&1
    return a

def main():
    bit=compressions=0
    for n in range(1,5):
        co=[(i,j) for i in range(n) for j in range(i,n)]
        for mask in range(1<<len(co)):
            c=inv(mat(n,co,mask))
            if c is None:continue
            bit+=1
            for a in range(n):
                ids=[i for i in range(n) if i!=a];k=len(ids)
                ce=[[c[i][j] for j in ids] for i in ids]
                for i in range(k):
                    for j in range(k):
                        g=F(i==j)+sum(ce[t][i]*ce[t][j] for t in range(k))
                        for sign in [-1,1]:
                            fact=sum((F(t==i)+sign*ce[t][i])*(F(t==j)+sign*ce[t][j]) for t in range(k))
                            assert g+2*sign*ce[i][j]==fact
                compressions+=1
    graphs=singular=flips=0;probchecks=0
    for n in range(2,6):
        co=list(combinations(range(n),2));totals={p:[F(0),F(0)] for p in [F(1,4),F(1,2),F(3,4)]}
        for mask in range(1<<len(co)):
            a=mat(n,co,mask);graphs+=1;k=n-rank(a)
            if k:
                singular+=1;found=False
                for ids in combinations(range(n),k-1):
                    b=[row[:] for row in a]
                    for j in ids:b[j][j]=1
                    if rank(b)==n-1:found=True;break
                assert found;flips+=1
            e=mask.bit_count()
            for p,out in totals.items():
                weight=p**e*(1-p)**(len(co)-e)
                if not any(a[0]):out[0]+=weight
                if a[0]==a[1]:out[1]+=weight
        for p,(isolated,twins) in totals.items():
            q=1-p;Q=p*p+q*q
            assert isolated==q**(n-1)
            assert twins==q*Q**(n-2)
            probchecks+=2
    assert F(3,4)>F(1,4)**2+F(3,4)**2
    return {'status':'PASS','nonsingular_symmetric_bit_matrices_n_le_4':bit,
      'principal_inverse_compressions':compressions,'simple_graphs_n_2_to_5':graphs,
      'singular_graphs_with_exact_corank_one_diagonal_repair':flips,'exact_lower_event_probabilities':probchecks,
      'control':'At p=1/4 the isolated-vertex exponential base exceeds the sign-matrix collision base; importing that rate unchanged would be false.',
      'limits':'Finite exact algebra and probabilities only. No eigenvalue asymptotics, typical-event bounds, or full theorem verified by these tests.'}

if __name__=='__main__':print(json.dumps(main(),indent=2))
