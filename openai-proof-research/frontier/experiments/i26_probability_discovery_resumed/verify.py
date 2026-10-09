"""Read-only integrity verification; the mathematical diagnostics are separate."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i26_probability_discovery_resumed';E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
counts={};failures=[];drift=[]
def check(ok,what):
 if not ok:failures.append(what)
def check_entry(x,path=None):
 p=R/(path or x['path']);check(p.is_file(),str(p)+' missing')
 if p.is_file():
  b=p.read_bytes();check(sha(b)==x['sha256'],str(p)+' SHA256 mismatch')
  if 'bytes' in x:check(len(b)==x['bytes'],str(p)+' byte count mismatch')
seal_path=S/'artifact-seal.json';raw=seal_path.read_bytes();check(sha(raw)==(S/'artifact-seal.sha256').read_text().strip(),'seal digest')
sealed=json.loads(raw);counts['sealed_artifacts']=len(sealed['files'])
for x in sealed['files']:check_entry(x)
expected={x['path'] for x in sealed['files']}
excluded={str((S/'artifact-seal.json').relative_to(R)),str((S/'artifact-seal.sha256').relative_to(R)),str((E/'verification.json').relative_to(R))}
actual={str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
actual.add('frontier/iterations/i26-probability-discovery-resumed.md')
check(actual-excluded==expected,'resumed file inventory differs from seal')
original=json.loads((S/'original-readonly-manifest.json').read_text());counts['original_readonly_files']=len(original)
for x in original:check_entry(x)
old_actual={str(p.relative_to(R)) for root in [R/'frontier/sources/i26_probability_discovery',R/'frontier/experiments/i26_probability_discovery'] for p in root.rglob('*') if p.is_file()}
check(old_actual=={x['path'] for x in original},'original I26 file inventory changed')
for name in ['initial-inputs-manifest.json','current-inputs-manifest.json']:
 m=json.loads((S/name).read_text());counts[name]=len(m)
 for x in m:
  check_entry(x,x['snapshot'])
  p=R/x['path']
  if p.is_file() and sha(p.read_bytes())!=x['sha256']:
   if x['path']=='frontier/TEN-FINDINGS.md':drift.append(dict(snapshot_set=name,path=x['path'],frozen_sha256=x['sha256'],live_sha256=sha(p.read_bytes()),classification='shared-ledger drift; not a changed frozen premise'))
   else:check(False,'non-ledger live dependency changed: '+x['path'])
tree=json.loads((S/'current-inputs/sources/preprints-tree.json').read_text());check(tree.get('truncated') is False,'complete tree truncated');T={x['path']:x for x in tree['tree']}
counts['inventory_manuscripts']=sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree['tree'])
m=json.loads((S/'pinned-manifest.json').read_text());counts['pinned_files']=len(m['files']);counts['pinned_manuscripts']=len({x['path'].split('/')[1] for x in m['files']})
check(m['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','wrong upstream pin')
for x in m['files']:
 p=S/'pinned'/x['path'];b=p.read_bytes();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 check(sha(b)==x['sha256'] and len(b)==x['bytes'],'pinned SHA/size: '+x['path'])
 check(g==x['git_blob']==T[x['path']]['sha'],'pinned Git identity: '+x['path'])
 check(x['url']=='https://raw.githubusercontent.com/openai/math/'+m['pin']+'/'+x['path'],'unpinned raw URL: '+x['path'])
for name in ['statement-contracts.json','read-passages.json']:
 m=json.loads((S/name).read_text());counts[name]=len(m)
 for x in m:
  b=''.join((R/x['path']).read_text().splitlines(keepends=True)[x['start_line']-1:x['end_line']])
  check(sha(x['text'].encode())==x['sha256'],'stored excerpt SHA: '+x['path'])
  check((x['text']==b) if name=='read-passages.json' else x['text'] in b,'excerpt/source mismatch: '+x['path'])
retrieved=json.loads((S/'literature/retrieval-manifest.json').read_text());counts['primary_retrievals']=len(retrieved)
for x in retrieved:
 if 'error' in x:check(False,'primary retrieval error: '+str(x));continue
 p=S/'literature'/x['name'];check(sha(p.read_bytes())==x['sha256'] and p.stat().st_size==x['bytes'],'primary identity: '+x['name'])
 if x['name'].endswith('.pdf'):check('v'+str(x['arxiv_version']) in x['url'],'primary PDF URL lacks version')
diag=json.loads((E/'diagnostics.json').read_text());check(diag['status']=='PASS','diagnostics do not say PASS')
result=dict(status='PASS' if not failures else 'FAIL',counts=counts,failures=failures,shared_index_drift=drift,diagnostics=diag['counts'],scope='Integrity and retained diagnostics only; not a proof or significance verdict.')
print(json.dumps(result,indent=2));raise SystemExit(bool(failures))
