#!/usr/bin/env python3
"""Exact diagnostic for the split (2,3) seed; not a theorem/review gate.

Standard library only. Prints JSON; never writes files.
"""
from fractions import Fraction as Q
import json

N = 6
def zero(): return [[Q(0) for _ in range(N)] for _ in range(N)]
def unit(i,j):
    a=zero(); a[i][j]=Q(1); return a
def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
def sub(a,b): return [[a[i][j]-b[i][j] for j in range(N)] for i in range(N)]
def flat(a): return sum(a,[])
def rank(rows):
    a=[list(row) for row in rows]
    if not a: return 0
    k=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(k,len(a)) if a[i][j]),None)
        if pivot is None: continue
        a[k],a[pivot]=a[pivot],a[k]
        v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j]
            if v: a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a): break
    return k

I=zero()
for i in range(N): I[i][i]=1
S=zero();T=zero();weights=[Q(2),Q(3),Q(5)]
for i in range(3):
    S[i+3][i]=weights[i];S[i][i+3]=1/weights[i]
    T[(i+1)%3][i]=1;T[3+(i-1)%3][3+i]=1
assert mul(S,S)==I and mul(mul(T,T),T)==I
R=mul(mul(S,T),mul(S,T));R2=mul(mul(S,R),S)
assert all(R[i][j]==R2[i][j]==0 for i in range(N) for j in range(N) if i!=j)
signatures=[(R[i][i],R2[i][i]) for i in range(N)]
assert len(set(signatures))==6
E=[unit(i,j) for i in range(N) for j in range(N)]
adS=[flat(sub(mul(e,S),mul(S,e))) for e in E]
adT=[flat(sub(mul(e,T),mul(T,e))) for e in E]
inner=[a+b for a,b in zip(adS,adT)]
rt=rank(adT);ri=rank(inner)
combined=inner+[[Q(0)]*36+b for b in adT]
assert (rank(adS),rt,ri,rank(combined))==(18,24,35,42)
chosen=[];basis=inner[:];current=ri
for i,b in enumerate(adT):
    new=[Q(0)]*36+b
    if rank(basis+[new])>current:
        basis.append(new);current+=1;chosen.append([i//6,i%6])
    if len(chosen)==2: break
assert current==37
print(json.dumps({"S_squared_identity":True,"T_cubed_identity":True,
  "joint_diagonal_signatures":[[str(x),str(y)] for x,y in signatures],
  "ad_S_rank":18,"ad_T_rank":24,"simultaneous_inner_rank":35,
  "combined_rank":42,"transverse_quotient_dimension":7,
  "two_split_conjugation_directions_matrix_units":chosen,
  "limits":"Split witness and finite ranks only. Generic division descent, formal identities, and infinite scheduling require the written argument."},indent=2))
