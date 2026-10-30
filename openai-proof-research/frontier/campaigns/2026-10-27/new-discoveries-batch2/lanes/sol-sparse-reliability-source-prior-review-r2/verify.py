"""Run only through the assigned helper_guard.py; finite diagnostics are not proof."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib,json,datetime,sys
P=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def H(m):
 k=(m-1)//2
 return [(0,1)]+[(v,t) for v in range(2,k+2) for t in [0,1]]+([(2,3)] if m%2==0 else [])
def U(edges):
 # Exact independent uniform edge-mask experiment at p=1/2. Enumerate paths directly.
 verts=set(v for e in edges for v in e); bad=0
 for mask in range(1<<len(edges)):
  adj={v:set() for v in verts}
  for i,(v,w) in enumerate(edges):
   if mask>>i&1:adj[v].add(w);adj[w].add(v)
  success=1 in adj[0] or bool(adj[0]&adj[1]) or any(adj[v]&adj[1] for v in adj[0])
  bad+=not success
 return Q(bad,1<<len(edges))
def check():
 u={m:U(H(m)) for m in range(5,13)}
 # Independent closed form control; not the oracle used in the actual inequality test.
 for m,v in u.items():assert v==Q(1,2)*Q(3,4)**((m-1)//2)*(Q(8,9) if m%2==0 else 1)
 deleted=H(10);deleted.remove((2,0))
 assert 1-U(deleted)==Q(413,512) and 1-u[9]==Q(431,512)
 # 2025 Lemma23(iii): n=8,m=12,x=1 is inside its printed domain.
 m=12;x=1;r=p=Q(1,2)
 rhs=r*r*u[m-x-2]+2*p*r**(x+1)*sum(comb(x,i)*p**i*u[m-2-x-i] for i in range(x+1))
 assert rhs<u[m] and rhs-u[m]==-Q(3,1024)
 return {'U12':str(u[12]),'lemma23iii_RHS':str(rhs),'RHS_minus_LHS':str(rhs-u[12]),'n':8,'m':12,'x':1,'rho':'1/2','deleted_H10_R':'413/512','H9_R':'431/512','edge_mask_models':8,'finite_diagnostic_only':True}
def frozen_check():
 j=json.loads((P/'freeze-before.json').read_text())
 for row in j['files']:
  assert sha(Path(row['original']))==row['sha256'],row['original']
  assert sha(P/row['copy'])==row['sha256'],row['copy']
 return len(j['files'])
if __name__=='__main__':
 result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_pairs_verified':frozen_check(),'diagnostics':check()}
 if '--manifest' in sys.argv:
  j=json.loads((P/'final-manifest.json').read_text());excluded={'final-manifest.json','manifest-verification.json'}
  assert set(j['excludes'])==excluded
  actual={str(f.relative_to(P)) for f in P.rglob('*') if f.is_file() and str(f.relative_to(P)) not in excluded}
  assert actual==set(j['files'])
  for rel,h in j['files'].items():assert sha(P/rel)==h,rel
  result.update(manifest_sha256=sha(P/'final-manifest.json'),files_verified=len(actual),explicit_exclusions=sorted(excluded),status='PASS')
  (P/'manifest-verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
