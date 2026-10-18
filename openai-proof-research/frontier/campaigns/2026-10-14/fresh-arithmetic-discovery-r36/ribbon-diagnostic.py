#!/usr/bin/env python3
"""MIT. Exact finite ribbon-turn checks; the uniform topology proof is in the candidate."""
import json

def check(g,word):
 order=[s for i in range(1,g+1) for s in [2*i-1,-2*i,-(2*i-1),2*i]]
 pos={x:i for i,x in enumerate(order)}
 turns=[tuple(sorted((pos[-x],pos[y]))) for x,y in zip(word,word[1:]+word[:1])]
 assert len({x for p in turns for x in p})==2*len(turns)
 for i,(a,b) in enumerate(turns):
  for c,d in turns[i+1:]:assert not (a<c<b<d or c<a<d<b)
 boundary=[1]
 while True:
  v=order[(pos[-boundary[-1]]+1)%len(order)]
  if v==1:break
  boundary.append(v)
 expected=[s for i in range(1,g+1) for s in [2*i-1,2*i,-(2*i-1),-2*i]]
 assert boundary==expected
 return {'genus':g,'word':word,'turns':turns,'noncrossing':True,'boundary_is_standard_relation':True}

if __name__=='__main__':
 cases=[]
 for g in range(2,7):
  cases.extend([check(g,[2,4]),check(g,[1,2,3,4])])
  for i in range(3,g+1):cases.extend([check(g,[1,2,3,4,2*i-1]),check(g,[1,2,3,4,-2*i])])
 print(json.dumps({'status':'PASS_FINITE_DIAGNOSTIC_ONLY','cases':cases,'limit':'Base curves and boundary conventions only; powers are justified by actual boundary-fixing Dehn twists in the proof.'},indent=2))
