import json,pathlib
from fractions import Fraction
P=pathlib.Path(__file__).parent
N=200;a=[1]+[0]*N
for j in range(1,N+1):
 for m in range(j,N+1):a[m]+=a[m-j]
 for twice in range(2):
  for m in range(N,2*j-1,-1):a[m]-=a[m-2*j]
tri={m*(m+1)//2 for m in range(N+1) if m*(m+1)//2<=N}
assert all(a[k]==int(k in tri) for k in range(N+1))
out={'384758':{'executed':True,'method':'Exact formal product truncation; factors j<=200 suffice through degree 200','degree':N,'nonzero_degrees':[k for k in range(N+1) if a[k]],'all_coefficients_zero_or_one':True,'all_scope_proof_status':'Not inferred from finite check; classical Gauss identity is the routine full-scope route, primary proof-body not cleared'}}
rows=[]
for d in [2,4,6,8,10,20,100]:
 vals=[Fraction(d,2)*(1-Fraction(l,d))+Fraction(d,2)*Fraction(l,d) for l in range(d+1)]
 assert all(x==Fraction(d,2) for x in vals)
 rows.append({'d':d,'possible_negative_counts_checked':d+1,'l1_norm_when_half_positive_basis_vectors_seen':str(vals[0])})
out['384743']={'executed':True,'states':rows,'argument':'Use e1,...,ed plus d copies of -(1/d,...,1/d). Every vector has l1 norm 1 and total is zero. In any order, when k=d/2 distinct positive basis vectors have appeared and l negative vectors, norm = k*(1-l/d)+(d-k)*l/d=d/2. This contradicts a uniform O(sqrt d) bound over arbitrary norms as even d grows. Classical norm-scope obstruction; credit zero.','all_scope_status':'Elementary symbolic identity above; checks are confirmation, not inference from instances.'}
(P/'bounded-checks.json').write_text(json.dumps(out,indent=2)+'\n');print('two bounded checks PASS')
