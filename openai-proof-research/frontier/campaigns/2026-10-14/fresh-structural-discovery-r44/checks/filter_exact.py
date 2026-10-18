#!/usr/bin/env python3
"""MIT. Exact finite identities; not adaptive existence or the universal theorem."""
from fractions import Fraction as F
import itertools,json

def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
def tr(a):return list(map(list,zip(*a)))
def mm(a,b):return [[dot(x,y) for y in tr(b)] for x in a]
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def neg(a):return [[-x for x in r] for r in a]

def check(seq):
 d=3;n=len(seq);sig=F(5,13);m=d+n
 R=[r+[F(0)]*n for r in eye(d)];rows=[];states=[R];ys=[]
 for i,v in enumerate(seq):
  b=[sig*x for x in v];c=F(12,13) if any(v) else F(1);eta=1/(1+c)
  C=[[F(a==j)-eta*b[a]*b[j] for j in range(d)] for a in range(d)]
  row=[eta*dot(b,col) if j>=d else F(0) for j,col in enumerate(tr(R))]
  assert all(x==0 for x in row[d+i:]);rows.append(row)
  ys.append([-dot(b,col)+(c if j==d+i else 0) for j,col in enumerate(tr(R))][d:])
  R=mm(C,R)
  for j in range(d):R[j][d+i]+=b[j]
  assert mm(R,tr(R))==eye(d);states.append(R)
 for j in range(m):assert sum(r[j]**2 for r in rows)<=sig**2
 final=[r[d:] for r in R]
 assert add(mm(tr(ys),ys),mm(tr(final),final))==eye(n)
 for eps in itertools.product((-1,1),repeat=n):
  x=[F(0)]*m;partial=[F(0)]*d
  for i,(v,e) in enumerate(zip(seq,eps)):
   x[d+i]=e+dot(rows[i],x)
   partial=[a+e*sig*z for a,z in zip(partial,v)]
   assert [dot(r,x) for r in states[i+1]]==partial
  y=[dot(row,x[d:]) for row in ys]
  for i,v in enumerate(seq):
   c=F(12,13) if any(v) else F(1);eta=1/(1+c)
   assert eta*(x[d+i]+y[i])==eps[i]
 return 2**n
basis=[tuple(F(i==j) for i in range(3)) for j in range(3)]
pool=basis+[(F(3,5),F(4,5),F(0)),(F(0),F(5,13),F(12,13)),(F(0),)*3]
seqs=[pool,pool[::-1],[pool[0]]*6,[pool[i%6] for i in (0,3,1,4,2,5,3,4)]]
num=sum(check(s) for s in seqs)
# Endpoint-only law negative control: signs are one common fair bit on
# (e1,...,ed,-e1,...,-ed). Endpoint=0, hard prefix norm<=sqrt(d),
# but the prefix at d has variance d in direction (1,...,1)/sqrt(d).
control=[{'d':d,'endpoint_squared_norm':0,'maximum_prefix_squared_norm':d,'variance_in_unit_diagonal_direction':d} for d in (1,2,4,16,64)]
print(json.dumps({'status':'PASS','arithmetic':'exact fractions','sequences':len(seqs),'sign_patterns':num,'checks':['coisometry','predictor causal support','predictor column bound','unclipped algebraic cancellation','passive contraction identity','coefficient-to-sign identity'],'endpoint_only_negative_control':control,'limits':'No adaptive-sign existence, Gaussian energy, minimax, subgaussian law or universal tree theorem is tested.'},indent=2))
