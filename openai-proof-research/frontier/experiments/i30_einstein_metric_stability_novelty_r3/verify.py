"""Read-only dependency verification; writes only this review's experiment output.
--seal is a one-time packaging action, not needed to reproduce verification.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[3]; E=Path(__file__).resolve().parent
S=R/'frontier/sources/i30_einstein_metric_stability_novelty_r3'
report=R/'frontier/reviews/i30-einstein-metric-stability-novelty-r3.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def row(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(R)),sha256=sha(b),bytes=len(b))
def scope(p):return p==report or S in p.parents or E in p.parents
seal=S/'artifact-seal.json';out=E/'verification.json'
if '--seal' in sys.argv:
 files=[report]+[p for root in (S,E) for p in root.rglob('*') if p.is_file() and p not in (seal,out) and '__pycache__' not in p.parts]
 assert all(scope(p) for p in files)
 dump(seal,dict(policy='Excludes self, regenerated verification.json and Python bytecode; all other assigned artifacts included.',files=[row(p) for p in sorted(files)]))
errors=[];drift=[];counts={}
def verify(x,pathkey='path'):
 p=R/x[pathkey]
 if not p.exists():errors.append('missing '+str(p.relative_to(R)));return
 b=p.read_bytes()
 if sha(b)!=x['sha256'] or ('bytes' in x and len(b)!=x['bytes']):errors.append('hash/bytes '+str(p.relative_to(R)))
inputs=json.loads((S/'input-manifest.json').read_text())['files']
for x in inputs:
 verify(dict(x,path=x['frozen']))
 p=R/x['path']
 if not p.exists() or sha(p.read_bytes())!=x['sha256']:
  (drift if x.get('shared') else errors).append('live input drift '+x['path'])
counts['frozen_inputs']=len(inputs)
deps=json.loads((S/'dependency-manifest.json').read_text())['files']
for x in deps:
 if x['path']=='frontier/TEN-FINDINGS.md':
  if sha((R/x['path']).read_bytes())!=x['sha256']:drift.append('shared dependency drift '+x['path'])
 else:verify(x)
counts['read_only_dependencies']=len(deps)
tree=json.loads((R/'sources/preprints-tree.json').read_text());assert not tree['truncated']
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
pinned=json.loads((S/'source-manifest.json').read_text())
assert pinned['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
for x in pinned['files']:
 verify(x,'local');b=(R/x['local']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if git!=x['git_blob'] or git!=blobs[x['path']]:errors.append('git identity '+x['path'])
 if '/'+pinned['pin']+'/' not in x['url']:errors.append('unpinned URL '+x['path'])
counts['selected_pinned_files']=len(pinned['files'])
primary=json.loads((S/'new-primary-manifest.json').read_text())
for x in primary:
 if 'path' in x:verify(x)
counts['new_primary_responses']=len(primary)
reads=json.loads((S/'read-passages.json').read_text())
for x in reads:
 p=R/x['path'];b=p.read_bytes();fragment=b''.join(b.splitlines(keepends=True)[x['start']-1:x['end']])
 if x['path']=='frontier/TEN-FINDINGS.md' and sha(b)!=x['file_sha256']:
  drift.append('shared live passage drift '+x['path']);continue
 if sha(b)!=x['file_sha256'] or sha(fragment)!=x['sha256']:errors.append('read passage '+x['path'])
counts['opened_passage_ranges']=len(reads)
assert sha((R/'frontier/iterations/i30-einstein-metric-stability.md').read_bytes())=='a8bdb8937745dc57d89d5ee1562299a8a7d888f1e6816c833f28776a14ebe8a9'
sealed=json.loads(seal.read_text())['files']
for x in sealed:
 if not scope(R/x['path']):errors.append('seal out of scope '+x['path'])
 verify(x)
counts['sealed_artifacts']=len(sealed)
actual={str(p.relative_to(R)) for p in [report]+[p for root in (S,E) for p in root.rglob('*') if p.is_file() and p not in (seal,out) and '__pycache__' not in p.parts]}
if actual!={x['path'] for x in sealed}:errors.append('seal file-set mismatch')
result=dict(status='PASS' if not errors else 'FAIL',counts=counts,errors=errors,shared_drift=drift,limits='Hashes and eight finite/formal diagnostics are not proof, significance, priority, or publication certification.')
dump(out,result);print(json.dumps(result,indent=2));sys.exit(bool(errors))
