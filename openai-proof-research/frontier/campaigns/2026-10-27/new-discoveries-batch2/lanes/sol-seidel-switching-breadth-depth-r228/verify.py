from pathlib import Path
from fractions import Fraction as F
import hashlib,json,itertools,datetime
p=Path(__file__).resolve().parent
m=json.loads((p/'finalmanifest.json').read_text())
for name,h in m.items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
for r in json.loads((p/'checks/freeze.json').read_text()):
 assert hashlib.sha256(Path(r['original']).read_bytes()).hexdigest()==r['sha256'],r['original']
 if r['copy']:assert hashlib.sha256((p/r['copy']).read_bytes()).hexdigest()==r['sha256']
a=json.loads((p/'checks/matrix-exact.json').read_text());S=a['matrix'];n=len(S)
assert n==28 and all(S[i][i]==0 for i in range(n))
assert all(S[i][j]==S[j][i] and abs(S[i][j])==1 for i in range(n) for j in range(i))
assert all(sum(row)==3 for row in S)
S2=[[sum(S[i][k]*S[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
S3=[[sum(S2[i][k]*S[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
assert all(S3[i][j]-5*S2[i][j]-29*S[i][j]+105*(i==j)==0 for i in range(n) for j in range(n))
# Symmetric S has only roots -5,3,7. Traces uniquely determine multiplicities14,7,7.
assert sum(S[i][i] for i in range(n))==0 and sum(S2[i][i] for i in range(n))==756
counts={}
for lam in [-5,3,7]:
 R=[[F(S[i][j]-lam*(i==j)) for j in range(n)] for i in range(n)];piv=[];r=0
 for j in range(n):
  k=next((k for k in range(r,n) if R[k][j]),None)
  if k is None:continue
  R[r],R[k]=R[k],R[r];v=R[r][j];R[r]=[x/v for x in R[r]]
  for k in range(n):
   if k!=r and R[k][j]:
    v=R[k][j];R[k]=[x-v*y for x,y in zip(R[k],R[r])]
  piv.append(j);r+=1
 free=[j for j in range(n) if j not in piv];count=0
 for tail in itertools.product([-1,1],repeat=len(free)-1):
  vals=(1,)+tail
  if all(abs(sum(R[i][j]*v for j,v in zip(free,vals)))==1 for i in range(r)):count+=2
 counts[str(lam)]=count;assert count==a['sign_intersections'][str(lam)]['total_sign_vectors']
assert counts=={'-5':0,'3':128,'7':0}
receipt={'status':'PASS','utc':str(datetime.datetime.now(datetime.timezone.utc)),'manifest_entries':len(m),'manifest_sha256':hashlib.sha256((p/'finalmanifest.json').read_bytes()).hexdigest(),'independent_fraction_elimination_counts':counts,'scope':'integrity and finite diagnostic only; no full Question A proof'}
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
