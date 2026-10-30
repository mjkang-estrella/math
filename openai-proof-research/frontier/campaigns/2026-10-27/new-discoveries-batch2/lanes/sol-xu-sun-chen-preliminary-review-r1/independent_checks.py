"""Independent exact derivation; stdlib only. Run under the designated guard.

Dense polynomial arithmetic, rational parameter derivation, and repeated monic
synthetic division are deliberately different from the candidate's binomial sum.
No evaluation at sampled real arguments is used.
"""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import json

L = Path(__file__).resolve().parent
def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a
def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for k,v in enumerate(a): c[k]+=v
    for k,v in enumerate(b): c[k]+=v
    return trim(c)
def scale(a,s): return trim([s*v for v in a])
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b): c[i+j]+=v*w
    return trim(c)
def mono(n,v=1): return [F(0)]*n+[F(v)]
def divide_at_one(a):
    # Horner synthetic division, descending traversal, exact remainder.
    q=[F(0)]*(len(a)-1); q[-1]=a[-1]
    for k in range(len(q)-2,-1,-1): q[k]=a[k+1]+q[k+1]
    return trim(q), a[0]+q[0]
def derive(A,B,C,n,p):
    # z=epsilon*x^2=(t^n-1)/C; t'=2epsilon*C*x/(n*t^(n-1)).
    # U=A*x/(B+t^p). F'=1/(1+z).
    # U'=A*(B+(1-2p/n)t^p+(2p/n)t^(p-n))/(B+t^p)^2.
    # Multiply U'-F' by positive t^(n-p)*(B+t^p)^2*(1+z).
    D=add([B],mono(p))
    W=add(add(mono(n-p,B),mono(n,1-F(2*p,n))),[F(2*p,n)])
    E=add([1-1/C],mono(n,1/C))
    return add(scale(mul(W,E),A),scale(mul(mono(n-p),mul(D,D)),-1))

P=derive(F(53,35),F(18,35),F(109,105),109,53)
# The positive normalization connecting the generic formula to printed P.
P=scale(P,109**2*35**2)
assert all(v.denominator==1 for v in P)
P=[int(v) for v in P]
expected={0:786520,56:-3433500,109:5698350,162:-14554225,165:10918530,218:584325}
assert {i:v for i,v in enumerate(P) if v}==expected
Q=P[:]; remainders=[]
for _ in range(4):
    Q,r=divide_at_one(Q); remainders.append(int(r)); assert r==0
assert len(Q)==215 and all(v.denominator==1 and v>0 for v in Q)
Q=[int(v) for v in Q]
assert mul(Q,[1,-4,6,-4,1])==P
assert sum(Q)>0 # nonzero remainder on attempting a fifth division
assert min(Q)==584325 and Q[0]==786520 and Q[-1]==584325
# Compare only after constructing and validating the independent quotient.
candidate=json.loads((L/'frozen/certificate.json').read_text())
assert Q==candidate['quotient_coefficients_low_to_high']
assert candidate['minimum_coefficient']==min(Q)
# Reconstruct the nearby source method too. Its cubic factor reverses sign
# on (0,1); this explains why Thm5 is a lower bound rather than the target upper.
S=derive(F(7,5),F(2,5),F(1),15,7)
S=scale(S,75)
assert S[:8]==[0]*8
T=S[8:] # the source explicitly removes the positive factor v^8
for _ in range(3): T,r=divide_at_one(T); assert r==0
assert [int(v) for v in T]==[12,36,72,120,180,252,336,394,426,432,412,366,294,196,147,105,70,42,21,7]
assert all(v>0 for v in T)
# Endpoint identity, exact squared comparison.
assert F(11445,109**2)==F(105,109)<1
result={'utc':datetime.now(timezone.utc).isoformat(),'status':'PASS',
 'method':'generic rational derivative numerator; dense exact arithmetic; four synthetic divisions',
 'degree_P':len(P)-1,'sparse_P':expected,'division_remainders':remainders,
 'degree_Q':len(Q)-1,'Q_low_to_high':Q,'minimum':min(Q),
 'minimum_indices':[i for i,v in enumerate(Q) if v==min(Q)],
 'constant':Q[0],'exact_root_multiplicity':4,'Q_at_one':sum(Q),
 'candidate_coefficient_list_agrees':True,'source_cubic_quotient_agrees':True,
 'scope':'finite exact algebra and endpoint arithmetic; calculus justified in review.md'}
(L/'independent-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='Q_low_to_high'}))
