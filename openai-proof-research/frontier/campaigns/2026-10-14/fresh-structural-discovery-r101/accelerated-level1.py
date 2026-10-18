"""Explore one exact sufficient rule for (1->3,2) conditional cards."""
from itertools import combinations
import json
S=frozenset([(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)])
def orient(s,k):return frozenset(((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in s)
def norm(s):
 a=min(x for x,y in s);b=min(y for x,y in s);return tuple(sorted((x-a,y-b) for x,y in s))
def canon(s):return min(norm(orient(s,k)) for k in range(8))
shapes={frozenset(norm(orient(S,k))) for k in range(8)}
def targets(A,n):
 return {B for sh in shapes for a in A for x,y in sh if len(A&(B:=frozenset((u+a[0]-x,v+a[1]-y) for u,v in sh)))>=n}
triples={canon(a) for a in combinations(S,3)};fours=set()
for a in triples:
 A=frozenset(a)
 for t in targets(A,2):
  for z in t-A:fours.add(canon(A|{z}))
cards={}
def add(A,T):
 ca=canon(A)
 for k in range(8):
  AA=orient(A,k);x=min(u for u,v in AA);y=min(v for u,v in AA)
  if norm(AA)==ca:
   TT=frozenset((u-x,v-y) for u,v in orient(T,k));cards.setdefault(ca,set()).add(TT)
for a in combinations(S,3):add(frozenset(a),S)
raw=0
for m in fours:
 M=frozenset(m);ts=sorted(targets(M,3),key=lambda t:tuple(sorted(t)))
 for i,j,k in combinations(range(len(ts)),3):
  es=[ts[z]-M for z in (i,j,k)]
  if any(es[a]&es[b] for a,b in combinations(range(3),2)):continue
  T=M|ts[i]|ts[j]|ts[k]
  for p in M:add(M-{p},T);raw+=1
records=[]
for a,ts in sorted(cards.items()):
 A=frozenset(a);minimal=[]
 for T in sorted(ts,key=lambda t:(len(t),tuple(sorted(t)))):
  if not any(U<=T for U in minimal):minimal.append(T)
 es=[T-A for T in minimal];first=min(es,key=len);good=True
 for x in first:
  others=[e for e in es if x not in e]
  if not others or set.intersection(*map(set,others)):good=False;break
 records.append({'required':a,'cards':len(ts),'minimal_cards':len(minimal),'no_two_cell_transversal':good})
print(json.dumps({'raw_rules':raw,'required_patterns':len(records),'new_two_required_patterns':[r for r in records if r['no_two_cell_transversal']],'records':records},indent=2))
