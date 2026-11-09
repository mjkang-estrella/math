from pathlib import Path
import json, math, hashlib
from fractions import Fraction
L=Path(__file__).resolve().parent
# Independently transcribed from the displayed graph, not candidate U or c arrays.
edges=[(1,2),(0,3),(1,3),(2,3),(3,4),(0,5),(2,5),(3,5),(1,6),(2,6),(4,6),(5,7),(0,8),(3,8),(4,8),(5,8),(1,9),(5,9),(7,9)]
assert len(set(frozenset(e) for e in edges))==19 and all(a!=b for a,b in edges)
states=[tuple((s>>i)&1 for i in range(10)) for s in range(1024)]
index={s:i for i,s in enumerate(states)}
adj=[sorted(b if a==i else a for a,b in edges if i in (a,b)) for i in range(10)]
transition=[];drift=[]
for state in states:
 destinations=[]
 for vertex in range(10):
  pool=adj[vertex]+([vertex] if len(adj[vertex])%2==0 else [])
  replacement=int(sum(state[j] for j in pool)>len(pool)//2)
  dest=list(state);dest[vertex]=replacement
  destinations.append(index[tuple(dest)])
 transition.append(destinations)
 drift.append(sum(states[d][1]-state[1] for d in destinations))
assert max(map(abs,drift))==1
mass=[2**sum(s)*3**(10-sum(s)) for s in states];W=5**10
assert sum(mass)==W
coeff=[]
for k in range(241):
 assert sum(mass)==W*10**k
 following=[0]*1024
 for source,amount in enumerate(mass):
  for destination in transition[source]:following[destination]+=amount
 c=sum(following[s]*states[s][1] for s in range(1024))-10*sum(mass[s]*states[s][1] for s in range(1024))
 assert c==sum(mass[s]*drift[s] for s in range(1024))
 assert abs(c)<=W*10**k
 coeff.append(c);mass=following
F=math.factorial(240)
A=sum(8**k*(F//math.factorial(k))*c for k,c in enumerate(coeff))
B=sum(80**k*(F//math.factorial(k)) for k in range(241))
C=121*80**241;D=19521
assert Fraction(C,D*F)==Fraction(80**241,math.factorial(241))/(1-Fraction(80,242))
assert D*A-W*C>0
lo=Fraction(D*A-W*C,W*(D*B+C));hi=Fraction(D*A+W*C,W*D*B)
assert 10**6*(D*A-W*C)>18*W*(D*B+C)
assert 10**6*(D*A+W*C)<19*W*D*B
# Candidate data is first consulted only after independent generation.
candidate=json.loads((L/'frozen/certificate-results.json').read_text())
assert coeff==list(map(int,candidate['coefficients']))
assert set(map(frozenset,edges))==set(map(frozenset,candidate['edges']))
assert {k:str(v) for k,v in dict(A=A,B=B,C=C,D=D,W=W).items()}==candidate['integer_certificate']
assert lo==Fraction(int(candidate['derivative_lower']['numerator']),int(candidate['derivative_lower']['denominator']))
assert hi==Fraction(int(candidate['derivative_upper']['numerator']),int(candidate['derivative_upper']['denominator']))
out=dict(passed=True,states=1024,edges=edges,adjacency=adj,degrees=list(map(len,adj)),coefficients=list(map(str,coeff)),integer_certificate={k:str(v) for k,v in dict(A=A,B=B,C=C,D=D,W=W).items()},positive_lower_numerator=True,all_coefficients_match=True,strict_integer_checks=True,method='tuple-state forward integer mass propagation; every vertex included even if destination unchanged')
(L/'independent-results.json').write_text(json.dumps(out,indent=2))
print('PASS: all 241 independently generated coefficients and all five certificate integers agree; positive numerator and both strict inequalities verified')
