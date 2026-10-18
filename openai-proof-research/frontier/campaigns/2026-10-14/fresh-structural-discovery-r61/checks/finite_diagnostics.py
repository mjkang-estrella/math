#!/usr/bin/env python3
"""MIT. Exact finite illustrations, not a universal compiler/algebra proof."""
from itertools import product,permutations
import json
I=9
def mul(a,b):
 r=0
 for i,j in product(range(2),repeat=2):
  z=0
  for k in range(2):z^=((a>>(2*i+k))&1)*((b>>(2*k+j))&1)
  r|=z<<(2*i+j)
 return r
def alt(xs):
 r=0
 for perm in permutations(range(len(xs))):
  v=I
  for i in perm:v=mul(v,xs[i])
  r^=v
 return r
basis=[I,2,4];span=[0]
for a in basis:span += [x^a for x in span[:]]
count=0
for xs in product(span,repeat=4):assert alt(xs)==0;count+=1
assert alt([I,2,4])==I # dimension threshold is real in this finite example
checks=0
for seed in range(16):
 labels=[('a',seed),('aa',(seed*3)%16),('ab',(seed*5+1)%16),('b',(seed*7+2)%16),('a',(seed+4)%16)]
 states=['','a'];edges={a:[[0]*2 for _ in range(2)] for a in 'ab'}
 combined={}
 for w,x in labels:combined[w]=combined.get(w,0)^x
 for p in states:
  for a in 'ab':
   v=p+a
   if any(w.startswith(v) and w!=v for w in combined):edges[a][states.index(p)][states.index(v)]^=I
   if v in combined:edges[a][states.index(p)][0]^=combined[v]
 for n in range(7):
  for letters in product('ab',repeat=n):
   w=''.join(letters);dp=[0]*(n+1);dp[0]=I
   for t in range(n):
    for label,x in labels:
     if w.startswith(label,t):dp[t+len(label)]^=mul(dp[t],x)
   row=[I,0]
   for a in w:
    new=[0,0]
    for u,v in product(range(2),repeat=2):new[v]^=mul(row[u],edges[a][u][v])
    row=new
   assert dp[n]==row[0],(seed,w,dp[n],row[0]);checks+=1
samples=[]
# E is an integer UPPER bound on log2 R_j; round log2 k<=4, log2(3k)<=5.
for g in [0,1,10,100,10**6,10**12]:
 h=2;hs=[h]
 for j in range(1,20):
  h=h*h
  E=20+10+g+8*(j-1)+5*g*j+200000*sum(hs[1:])+g*sum(hs)
  if h>E+12:break
  hs.append(h)
 else:raise AssertionError('sample did not stop')
 assert sum(hs)<=2*hs[-1] and h==hs[-1]**2
 samples.append({'g':g,'stopping_level':j,'h_j':str(h),'log2_R_upper':str(E),'margin_gt_12':True})
print(json.dumps({'status':'PASS','alternation_tuples':count,'threshold_negative_control':alt([I,2,4]),'automaton_word_cases':checks,'sample_growth_budgets':samples,'limits':'No finite-presentation compiler execution, no universal theorem or novelty validation.'},indent=2))
