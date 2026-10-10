#!/usr/bin/env python3
"""Read-only integrity and diagnostic verifier. Does not fetch, seal or write files."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i43_convex_isoperimetric_discovery';E=Path(__file__).resolve().parent
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(name):return json.loads((S/name).read_text())
seal=read('artifact-seal.json')
for row in seal['files']:
 p=R/row['path'];assert p.is_file(),str(p);assert digest(p)==row['sha256'],str(p)
inv=read('frozen/sources/preprints-tree.json');assert not inv['truncated'];assert len(inv['tree'])==13223
blobs={x['path']:x['sha'] for x in inv['tree'] if x['type']=='blob'}
manuscripts={x['path'].split('/')[1] for x in inv['tree'] if x['path'].startswith('preprints/') and len(x['path'].split('/'))>=2};assert len(manuscripts)==749
manifest=read('frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json');assert manifest['pin']==PIN;assert len(manifest['files'])==9340
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
actual={str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()};expected={x['path'] for x in manifest['files']};assert actual==expected
for row in manifest['files']:
 p=C/row['path'];assert p.stat().st_size==row['bytes'];assert digest(p)==row['sha256'];assert blob(p)==row['git_blob']==blobs[row['path']],row['path']
selected=read('selected-manifest.json');assert selected['pin']==PIN
for row in selected['files']:
 p=S/'pinned'/row['path'];assert digest(p)==row['sha256'];assert blob(p)==row['git_blob']==blobs[row['path']]
for row in read('source-contracts.json'):
 text=(S/'pinned'/row['path']).read_text()
 for label in row['labels']:assert '{'+label+'}' in text,(row['path'],label)
for row in read('read-passages.json'):
 p=S/row['path'];assert digest(p)==row['sha256'];lines=p.read_text().splitlines();out=[]
 for a,b in row['ranges']:out.extend(f'{i}: {lines[i-1]}' for i in range(a,min(b,len(lines))+1))
 assert (S/row['extract']).read_text()=='\n'.join(out)+'\n'
responses=read('responses.json')
for row in responses:
 if 'file' in row:assert digest(S/row['file'])==row['sha256']
 if 'matches_pinned' in row:assert row['ok'] and row['matches_pinned']
mutable={'frontier/TEN-FINDINGS.md','frontier/iterations/README.md','frontier/iterations/iteration43-convex-isoperimetric-discovery-task.json'}
drift=[]
for row in read('frozen-inputs.json'):
 p=S/'frozen'/row['path'];assert digest(p)==row['sha256'];original=R/row['path']
 if not original.exists() or digest(original)!=row['sha256']:
  if row['path'] in mutable:drift.append(row['path'])
  else:raise AssertionError('immutable original changed: '+row['path'])
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
proc=subprocess.run([sys.executable,str(E/'check.py')],check=True,capture_output=True,text=True,env=env)
assert proc.stdout==(E/'check-output.json').read_text();check=json.loads(proc.stdout)
print(json.dumps({'status':'PASS','scope':'Integrity and exact finite checks only; no analytic acceptance or priority certificate.','seal_artifacts':len(seal['files']),'inventory_entries':len(inv['tree']),'manuscripts':len(manuscripts),'corpus_files':len(expected),'selected_pinned_files':len(selected['files']),'primary_responses':len(responses),'successful_responses':sum(x['ok'] for x in responses),'fresh_pinned_responses':sum('matches_pinned' in x for x in responses),'read_passage_records':len(read('read-passages.json')),'exact_assertions':check['assertions'],'mutable_input_drift':drift},indent=2,sort_keys=True))
