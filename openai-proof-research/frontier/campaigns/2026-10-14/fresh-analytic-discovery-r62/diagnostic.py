#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Exact finite countercontrols for attempted identities, not asymptotic proofs."""
from fractions import Fraction as F
from collections import defaultdict
import json

def main():
 p=[F(1,2),F(1,3),F(1,6)];mass=defaultdict(F);escort=defaultdict(F)
 for a in range(3):
  for b in range(3):
   t=F(a)+F(b,2);w=p[a]*p[b];mass[t]+=w;escort[t]+=w*w
 squares={t:w*w for t,w in mass.items()}
 assert mass[F(1)]==F(1,4) and squares[F(1)]==F(1,16) and escort[F(1)]==F(5,144)
 zm=sum(squares.values());zw=sum(escort.values())
 assert squares[F(1)]/zm!=escort[F(1)]/zw
 rows=[]
 for k in range(2,10):
  n=2*k
  edges=[(i,(i+1)%n) for i in range(n)]
  def matchings(es):
   def rec(rem,chosen):
    if not rem:return [frozenset(chosen)]
    v=min(rem);out=[]
    for j,(a,b) in enumerate(es):
     if v in (a,b) and a in rem and b in rem:out+=rec(rem-{a,b},chosen+[j])
    return out
   return rec(set(range(n)),[])
  full=matchings(edges);cut=matchings(edges[:-1]);assert len(full)==2 and len(cut)==1
  loop=F(sum(a!=b for a in full for b in full),len(full)**2)
  assert loop==F(1,2)
  rows.append(dict(vertices=n,cycle_matchings=2,cut_matchings=1,winding_probability=str(loop)))
 # Heavy atom law's squared norm is exact; no floating-point entropy claim.
 heavy=[]
 for M in [2,4,16,256,65536]:
  norm=F(1,4)+F(1,4*M);assert F(1,4)<norm<=F(1,2)
  heavy.append(dict(M=M,collision_sum=str(norm)))
 print(json.dumps(dict(status='PASS_FINITE_SCOPED_DIAGNOSTICS',map_escort_at_one=str(squares[F(1)]/zm),symbol_escort_at_one=str(escort[F(1)]/zw),false_escort_identity_rejected=True,false_cut_law_identity_rejected=True,cycles=rows,heavy_atom=heavy,full_theorem_proved=False),indent=2))
if __name__=='__main__':main()
