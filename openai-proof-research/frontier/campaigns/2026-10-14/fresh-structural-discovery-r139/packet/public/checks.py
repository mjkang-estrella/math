"""Exact finite author support, not a proof/acceptance gate. Standard library, read-only."""
from itertools import combinations, product
from fractions import Fraction as F
import json

def parts(n,lo=1):
    if not n:yield ()
    for a in range(lo,n+1):
        for rest in parts(n-a,a):yield (a,)+rest

def blocks(sizes):
    start=0;out=[]
    for a in sizes:
        out.append(frozenset(range(start,start+a)));start+=a
    return out

def connected(n,E):
    seen={0}
    while True:
        nxt=seen|{v for a,b in E for u,v in [(a,b),(b,a)] if u in seen}
        if nxt==seen:return len(seen)==n
        seen=nxt

def psd(A):
    A=[list(map(F,r)) for r in A];n=len(A)
    for i in range(n):
        d=A[i][i]
        if d<0:return False
        if d==0:
            if any(A[i][j] for j in range(i+1,n)):return False
            continue
        for j in range(i+1,n):
            for k in range(j,n):
                A[j][k]=A[k][j]=A[j][k]-A[i][j]*A[i][k]/d
    return True

counts=dict(partition_slices=0,allowed_states=0,deleted_boundary_checks=0,exact_psd_checks=0,graph_realizations=0)
for N in range(2,10):
    U=frozenset(range(N))
    for sizes in parts(N):
        bs=blocks(sizes);s=sizes.count(1);nontrivial=sum(a>1 for a in sizes)
        if not nontrivial:continue
        for q in range(1,N):
            allsets=[frozenset(x) for x in combinations(range(N),q)]
            A={S for S in allsets if any(0<len(S&B)<len(B) for B in bs)}
            if not A:continue
            counts['partition_slices']+=1
            bound=N-(s if nontrivial==1 else max(s,2))
            assert bound>=2
            adj={}
            for S in A:
                near={S-{i}|{j} for i in S for j in U-S}
                adj[S]=near&A;b=len(near-A)
                mixed=[B for B in bs if 0<len(S&B)<len(B)]
                expected=0
                if len(mixed)==1:
                    B=mixed[0];r=len(S&B)
                    if r==1:expected+=sum(len(C)==1 and not(S&C) for C in bs)
                    if r==len(B)-1:expected+=sum(len(C)==1 and bool(S&C) for C in bs)
                elif len(mixed)==2:
                    B,C=mixed
                    expected+=int(len(S&B)==1 and len(S&C)==len(C)-1)
                    expected+=int(len(S&C)==1 and len(S&B)==len(B)-1)
                assert b==expected and b<=N-bound
                counts['deleted_boundary_checks']+=1
                if N<=6:
                    E=set()
                    for B in bs:
                        z=sorted(B);E.update(zip(z,z[1:]))
                    E.update((i,N if i in S else N+1) for i in U)
                    assert connected(N+2,E);counts['graph_realizations']+=1
            seen={next(iter(A))}
            while True:
                nxt=seen|set().union(*(adj[S] for S in seen))
                if nxt==seen:break
                seen=nxt
            assert seen==A
            counts['allowed_states']+=len(A)
            if N<=6:
                order=sorted(A,key=lambda S:tuple(sorted(S)));k=len(order)
                L=[[int(i==j)*len(adj[S])-int(T in adj[S]) for j,T in enumerate(order)]for i,S in enumerate(order)]
                B=[[k*L[i][j]-bound*(k*int(i==j)-1)for j in range(k)]for i in range(k)]
                assert psd(B);counts['exact_psd_checks']+=1
# Sharp two-element-block eigenfunction, every q at these sizes.
sharp=0
for N in range(2,13):
 for q in range(1,N):
    U=set(range(N));A={frozenset(S) for S in combinations(range(N),q) if len(set(S)&{0,1})==1}
    f={S:1 if 0 in S else -1 for S in A}
    for S in A:
        near={S-{i}|{j} for i in S for j in U-S}&A
        assert sum(f[S]-f[T] for T in near)==2*f[S]
    sharp+=1
# Exact connected triple cell, independently generated from fixed margins.
raw=[]
for inte in combinations(range(3),2):
 for c3 in combinations(range(3),2):
  for c4,c5 in product(range(3),repeat=2):
   E=frozenset({inte,(3,4)}|{(i,3)for i in c3}|{(c4,4),(c5,5)})
   if tuple(sum(i in e for e in E)for i in range(6))==(3,2,1,3,2,1):raw.append(E)
assert len(raw)==8
edge_strings=['03 04 05 12 13','02 03 05 13 14','02 03 04 13 15','01 04 05 13 23','01 03 05 14 23','01 03 04 15 23','01 03 05 13 24']
states=[frozenset({(3,4)}|{tuple(map(int,s))for s in row.split()})for row in edge_strings]
assert set(states)=={E for E in raw if connected(6,E)}
# Check general row-factor connectivity description on all graphs through 5 vertices.
row_factor_checks=0
for n in range(3,6):
 ed=list(combinations(range(n),2))
 for mask in range(1<<len(ed)):
    E={e for j,e in enumerate(ed)if mask>>j&1};remaining=set(range(3,n));cs=[]
    while remaining:
        C={min(remaining)}
        while True:
            D=C|{v for a,b in E for u,v in [(a,b),(b,a)]if u in C and v>=3}
            if C==D:break
            C=D
        cs.append(C);remaining-=C
    totals=[sum((i,w)in E for i in range(3)for w in C)for C in cs]
    isolated=[]
    for i in range(3):
        internal=sum(i in e and max(e)<3 for e in E)
        isolated.append(internal==0 and all(sum((i,w)in E for w in C)in(0,t)for C,t in zip(cs,totals)))
    criterion=all(t>0 for t in totals)and not any(isolated)
    assert criterion==connected(n,E);row_factor_checks+=1

def cellH(st,n):
    k=len(st);H=[[F(3*int(i==j))for j in range(k)]for i in range(k)];fib=[]
    for a in combinations(range(3),2):
        groups={}
        for i,E in enumerate(st):
            key=(tuple(sorted(e for e in E if not(set(e)&set(a)))),a in E,tuple(sum(tuple(sorted((v,w)))in E for v in a)for w in range(n)if w not in a))
            groups.setdefault(key,[]).append(i)
        fib.append(list(groups.values()))
        for ids in groups.values():
            for i in ids:
                for j in ids:H[i][j]-=F(1,len(ids))
    return H,fib
H,fib=cellH(states,6)
f=list(map(F,[1,1,-3,1,1,-3,2]));Hf=[sum(H[i][j]*f[j]for j in range(7))for i in range(7)]
q=sum(x*x for x in Hf)-sum(x*y for x,y in zip(f,Hf))
assert sum(f)==0 and q==F(-8,3)
# Characteristic polynomial by Newton identities; entirely rational.
M=[[F(int(i==j))for j in range(7)]for i in range(7)];tr=[];coef=[F(1)]
for k in range(1,8):
 M=[[sum(M[i][z]*H[z][j]for z in range(7))for j in range(7)]for i in range(7)]
 tr.append(sum(M[i][i]for i in range(7)))
 coef.append(-sum(coef[k-j]*tr[j-1]for j in range(1,k+1))/k)
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
want=[F(1)]
for fac in [[1,0],[1,-1],[1,F(-4,3)],[1,-2],[1,-2],[1,F(-8,3),F(14,9)]]:want=mul(want,fac)
assert coef==want
for r in [0,1,2,5,20]:
 st=[E|frozenset((3,v)for v in range(6,6+r))for E in states]
 assert all(connected(6+r,E)for E in st)
 assert cellH(st,6+r)[0]==H
print(json.dumps(dict(kind='finite exact author diagnostics; no mathematical gate',counts=counts,sharp_fibers=sharp,triple_full_states=8,triple_connected_states=7,triple_fibers=fib,triple_characteristic_coefficients=list(map(str,coef)),square_defect_uniform=str(q/7),row_factor_graphs=row_factor_checks,leaf_lifts=[0,1,2,5,20]),indent=2,sort_keys=True))
