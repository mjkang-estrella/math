from pathlib import Path
import json,math,heapq
L=Path(__file__).resolve().parent
# Integer lattice bases: all solutions, with displayed divisibility already absorbed.
bases=[((0,2,3),(1,0,0)),((1,1,1),(0,1,2)),((1,-1,0),(0,3,2)),((1,1,0),(0,1,3)),((1,0,3),(0,1,-1)),((2,0,3),(0,1,0)),((1,0,1),(0,3,1)),((3,4,0),(0,0,1)),((3,0,4),(0,1,0)),((1,-1,1),(0,3,1))]
lines=[(0,3,-2),(1,-2,1),(2,2,-3),(3,-3,1),(3,-1,-1),(3,0,-2),(3,1,-3),(4,-3,0),(4,0,-3),(4,1,-3)]
out=[]
for f,(v,w) in zip(lines,bases):
 assert sum(a*b for a,b in zip(f,v))==sum(a*b for a,b in zip(f,w))==0
 residues=[[p,q] for p in range(3) for q in range(3) if sorted((p*x+q*y)%3 for x,y in zip(v,w))==[0,1,2]]
 out.append(dict(line=f,basis=[v,w],parameter_residues_mod3=residues,quantifiers='all integers p,q with a>=12, a<b<d<2a, gcd(a,b,d)=1 and ratio in retained open segments; vertices handled separately'))
# AP formula independent DP checks; checks support the ordinary proof, not universality.
tested=0
for a in range(12,61):
 for t in range(1,(a-1)//2+1):
  if math.gcd(a,t)!=1:continue
  A=[0]*a
  for j in range(a):A[j*t%a]=((j+1)//2)*a+j*t
  top=max(A)+a+1;dp=[True]+[False]*top
  for n in range(1,top+1):dp[n]=any(n>=g and dp[n-g] for g in [a,a+t,a+2*t])
  assert all(dp[n]==(n>=A[n%a]) for n in range(top+1))
  tested+=1
(L/'symbolic-result.json').write_text(json.dumps(dict(lattices=out,AP_formula_DP_cases=tested),indent=2)+'\n')
print('lattice bases and AP checks',tested)
