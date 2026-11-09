#!/usr/bin/env python3
"""Dependency-free finite identity diagnostics; not a global proof."""
import math,json

def mul(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def dot(A,B):return sum(x*y for ar,br in zip(A,B) for x,y in zip(ar,br))
def err(A,B):return math.sqrt(sum((x-y)**2 for ar,br in zip(A,B) for x,y in zip(ar,br)))
def add(A,B):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(A,B)]
def transpose(A):return list(map(list,zip(*A)))

def inspect(T,label):
 m=len(T);I=[[float(i==j) for j in range(m)] for i in range(m)]
 B=[[dot(x,y) for y in T] for x in T]
 K=lambda Y:[[sum(mul(mul(X,Y),X)[i][j] for X in T) for j in range(m)] for i in range(m)]
 KX=[K(X) for X in T]
 V=[[dot(T[i],KX[j]) for j in range(m)] for i in range(m)]
 D=[[I[i][j]-V[i][j] for j in range(m)] for i in range(m)]
 row=[[0.]*m for _ in range(m)];col=[[0.]*m for _ in range(m)]
 for r in range(m):
  for s in range(m):
   prod=mul(T[r],T[s])
   E=[[prod[i][j]-sum(T[r][s][t]*T[t][i][j] for t in range(m)) for j in range(m)] for i in range(m)]
   row=add(row,mul(E,transpose(E)));col=add(col,mul(transpose(E),E))
 target=[[2*x for x in line] for line in D]
 deviation=max(err(row,target),err(col,target))
 if err(B,I)>1e-9 or deviation>1e-8:raise ValueError((label,'Gram identity failed',deviation))
 Z=[[float(i==0 and j==1)-float(i==1 and j==0) for j in range(m)] for i in range(m)]
 deriv=[[[sum(Z[a][r]*T[r][b][c]+Z[b][r]*T[a][r][c]+Z[c][r]*T[a][b][r] for r in range(m)) for c in range(m)] for b in range(m)] for a in range(m)]
 actual=sum(dot(M,M) for M in deriv);formula=3*dot(Z,Z)-6*dot(Z,K(Z))
 if abs(actual-formula)>1e-8:raise ValueError('skew derivative identity')
 return {'case':label,'dimension':m,'B_error':err(B,I),'row_column_error':deviation,'skew_derivative_error':abs(actual-formula),'C':sum(D[i][i] for i in range(m))}

rows=[]
for n in [3,4,6]:
 d=n-1
 Q=[[((1 if i<=k else -(k+1) if i==k+1 else 0)/math.sqrt((k+1)*(k+2))) for k in range(d)] for i in range(n)]
 T=[[[math.sqrt(n/(n-2))*sum(Q[i][a]*Q[i][b]*Q[i][c] for i in range(n)) for c in range(d)] for b in range(d)] for a in range(d)]
 row=inspect(T,f'simplex_n={n}')
 if abs(row['C']-(n-1)/(n-2))>1e-8:raise ValueError('simplex C')
 U=[[[dot(mul(T[a],T[b]),T[c]) for c in range(d)] for b in range(d)] for a in range(d)]
 scalar=(n-3)/(n-2)
 dev=math.sqrt(sum((U[a][b][c]-scalar*T[a][b][c])**2 for a in range(d) for b in range(d) for c in range(d)))
 if dev>1e-8:raise ValueError('simplex triple trace')
 row['triple_trace_error']=dev;rows.append(row)
print(json.dumps({'status':'PASS_FINITE_IDENTITY_DIAGNOSTICS_ONLY','cases':rows},indent=2))
