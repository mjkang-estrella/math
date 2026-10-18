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

import random
rng=random.Random(101)
def minimal(ts):
 out=[]
 for T in sorted(ts,key=lambda t:(len(t),tuple(sorted(t)))):
  if not any(U<=T for U in out):out.append(T)
 return out
def no2(es):
 if not es:return False
 if any(not e for e in es):return True
 for x in min(es,key=len):
  others=[e for e in es if x not in e]
  if not others or set.intersection(*map(set,others)):return False
 return True
level1={a:minimal(ts) for a,ts in cards.items()};cards={};witnesses=[]
for a,ts in sorted(level1.items()):
 A=frozenset(a)
 if not no2([T-A for T in ts]):continue
 for trial in range(80):
  order=list(ts);rng.shuffle(order);chosen=list(order)
  for T in order:
   new=[U for U in chosen if U!=T]
   if no2([U-A for U in new]):chosen=new
  envelope=A|frozenset().union(*chosen)
  witnesses.append(dict(required=a,children=len(chosen),envelope=len(envelope)))
  for pivot in A:add(A-{pivot},envelope)

level2={a:minimal(ts) for a,ts in cards.items()}
# Canonical placement of a card on a specified congruent required pair.
def placements(a,T,B):
 for k in range(8):
  aa=orient(a,k);tt=orient(T,k)
  first=min(aa)
  for b in B:
   dx,dy=b[0]-first[0],b[1]-first[1]
   moved=frozenset((x+dx,y+dy) for x,y in aa)
   if moved==B:yield frozenset((x+dx,y+dy) for x,y in tt)
def possible_thirds(A,pairtypes):
 out=set()
 for a in A:
  for pair in pairtypes:
   for k in range(8):
    pp=orient(pair,k)
    for u in pp:
     moved={(x+a[0]-u[0],y+a[1]-u[1]) for x,y in pp}
     out.update(moved-A)
 return out
def cuts2(es):
 if not es:return []
 out=set()
 for x in min(es,key=len):
  others=[e for e in es if x not in e]
  if not others:out.add((x,));continue
  for y in set.intersection(*map(set,others)):out.add(tuple(sorted({x,y})))
 return sorted(out)
history=[]
for round in range(10):
 triples2={canon(set(a)|{z}) for a in level2 for z in possible_thirds(set(a),level2)}
 old=level2;cards={a:set(ts) for a,ts in old.items()};positive=0
 for a in sorted(triples2):
  A=frozenset(a);placed=set()
  for pair in combinations(a,2):
   ca=canon(pair)
   for T in old.get(ca,[]):placed.update(placements(ca,T,frozenset(pair)))
  placed.update(level1.get(a,[]));ts=minimal(placed)
  if not no2([T-A for T in ts]):continue
  positive+=1
  for trial in range(4):
   order=list(ts);rng.shuffle(order);chosen=list(order)
   for T in order:
    new=[U for U in chosen if U!=T]
    if no2([U-A for U in new]):chosen=new
   envelope=A|frozenset().union(*chosen)
   for pivot in A:add(A-{pivot},envelope)
 level2={a:minimal(ts) for a,ts in cards.items()}
 report=[dict(required=a,cards=len(ts),no_two_cell_transversal=no2([T-set(a) for T in ts]),min_envelope=min(map(len,ts)),cuts=cuts2([T-set(a) for T in ts])) for a,ts in sorted(level2.items())]
 history.append(dict(round=round,triples=len(triples2),positive=positive,patterns=report))
 import sys
 print(round,[(r['required'],len(r['cuts'])) for r in report],file=sys.stderr,flush=True)
 if any(r['no_two_cell_transversal'] for r in report):break
print(json.dumps(dict(limits='Exploratory bounded sufficient-rule closure with deterministic random pruning; not exhaustive.',history=history),indent=2))
