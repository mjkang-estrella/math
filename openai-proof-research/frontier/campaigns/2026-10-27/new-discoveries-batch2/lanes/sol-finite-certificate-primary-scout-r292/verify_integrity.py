"""Separate final verifier. Must run under fixed helper_guard after final writes."""
import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text());errors=[]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
if actual!=set(manifest['files']):errors.append('manifest inventory mismatch')
for name,h in manifest['files'].items():
 if sha(L/name)!=h:errors.append('lane file changed: '+name)
records=json.loads((L/'bindings.json').read_text())
for r in records:
 for key in (['copy'] if r['kind']=='administrative' else ['original','copy']):
  p=pathlib.Path(r[key])
  if not p.exists() or sha(p)!=r['sha256']:errors.append('binding changed: '+str(p))
for p in (L/'sources').iterdir():
 if not any(r['original']==str(p) for r in records):errors.append('unbound source '+str(p))
# Replay complete fixed n=5 endpoint with a third, exhaustive-cut characterization of SC.
A=[[0,1,0,0,-1],[1,0,1,0,0],[0,-1,0,1,0],[0,0,-1,0,1],[0,0,0,1,0]]
def sc(M):
 for mask in range(1,(1<<5)-1):
  if not any((mask>>i)&1 and not((mask>>j)&1) and M[i][j] for i in range(5) for j in range(5)):return False
 return True
def ap(M):
 B=[[int(M[i][j]>0)+int(M[j][i]<0) for j in range(5)] for i in range(5)]
 return all(any(x>0 for x in row) for row in M) and all(any(M[i][j]>0 for i in range(5)) for j in range(5)) and sc(M) and sc(B)
assert ap(A) and sum(x!=0 for row in A for x in row)==9 and all(A[i][i]==0 for i in range(5))
for i in range(5):
 for j in range(5):
  if A[i][j]:
   C=[row[:] for row in A];C[i][j]=0;assert not ap(C)
receipt=dict(status='PASS' if not errors else 'FAIL',date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'manifest.json'),lane_files=len(manifest['files']),source_bindings=len(records),fixed_endpoint='PASS: exhaustive directed cuts; all 9 deletions fail; zero diagonal; 9>8',errors=errors,counts_unchanged={'additional':9,'total':39,'next':40})
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));assert not errors
