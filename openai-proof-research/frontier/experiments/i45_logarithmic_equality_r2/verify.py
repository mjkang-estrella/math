#!/usr/bin/env python3
"""Read-only replay. No network, downloads, writes, bytecode, or old-seal refresh."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i45_logarithmic_equality_r2'
E=Path(__file__).resolve().parent
REPORT=R/'frontier/reviews/i45-logarithmic-equality-r2.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(path):return json.loads((S/path).read_text())
seal=read('artifact-seal.json')
actual={str(p.relative_to(R)) for base in [S,E] for p in base.rglob('*') if p.is_file() and p!=S/'artifact-seal.json'}|{str(REPORT.relative_to(R))}
expected={row['path'] for row in seal['files']}
assert actual==expected,(actual-expected,expected-actual)
for row in seal['files']:assert sha(R/row['path'])==row['sha256'],row['path']
frozen=read('frozen-inputs.json')
assert {r['path'] for r in frozen if r['mutable']}==LEDGERS
drift=[]
for row in frozen:
 p=S/'frozen'/row['path'];assert sha(p)==row['sha256'],row['path']
 live=R/row['path']
 if not live.exists() or sha(live)!=row['sha256']:
  if row['mutable']:drift.append(row['path'])
  else:raise AssertionError('Immutable prior input changed: '+row['path'])
for row in read('frozen-ledger-replay.json'):
 assert row['path'] in LEDGERS and row['mutable']
 assert sha(S/'frozen'/row['path'])==row['sha256']
 assert row['status_lines']==[[i,line] for i,line in enumerate((S/'frozen'/row['path']).read_text().splitlines(),1) if any(w in line for w in ['6/10','six of ten','accepted','Accepted','R012'])]
inv=read('frozen/sources/preprints-tree.json')
assert not inv['truncated'] and len(inv['tree'])==13223
blobs={r['path']:r['sha'] for r in inv['tree'] if r['type']=='blob'}
papers={r['path'].split('/')[1] for r in inv['tree'] if r['path'].startswith('preprints/')}
assert len(papers)==749
manifest=read('frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
assert manifest['pin']==PIN
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
listed=subprocess.run(['rg','--files','--no-ignore',str(C)],check=True,capture_output=True,text=True).stdout.splitlines()
assert {str(Path(p).relative_to(C)) for p in listed}=={r['path'] for r in manifest['files']}
assert len(listed)==9340
for row in manifest['files']:
 p=C/row['path']
 assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
 assert blob(p)==row['git_blob']==blobs[row['path']],row['path']
selected=read('selected-manifest.json');assert selected['pin']==PIN
for row in selected['files']:
 p=S/'pinned'/row['path']
 assert sha(p)==row['sha256'] and blob(p)==row['git_blob']==blobs[row['path']]
for row in read('source-contracts.json'):
 text=(S/'pinned'/row['path']).read_text()
 for label in row['labels']:assert '{'+label+'}' in text,label
for row in read('read-passages.json'):
 p=S/row['path'];assert sha(p)==row['sha256'];lines=p.read_text().splitlines()
 extract='\n'.join(f'{i}: {lines[i-1]}' for a,b in row['ranges'] for i in range(a,b+1))+'\n'
 assert extract==(S/row['extract']).read_text(),row['path']
responses=read('responses.json')
for row in responses:
 if 'sha256' in row:assert sha(S/row['file'])==row['sha256']
 if 'identical_to_i44' in row:
  oldpath=row['file'].removeprefix('current/')
  old=S/'frozen/frontier/sources/i44_logarithmic_equality_polytopes'/oldpath
  assert ((S/row['file']).read_bytes()==old.read_bytes())==row['identical_to_i44']
 if row['file'].startswith('current/fresh/') and row['ok']:
  pinpath=S/'pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build'/Path(row['file']).name
  assert (S/row['file']).read_bytes()==pinpath.read_bytes()
for row in read('versions.json'):
 assert sha(S/row['file'])==row['sha256'] and (S/row['pdf']).exists()
for row in read('external-contracts.json'):
 p=S/row['file'];assert sha(p)==row['sha256']
 for label in row['labels']:assert label in p.read_text(),(row['file'],label)
assert (S/'brief.txt').read_text()==(S/'i45-brief-prefix.txt').read_text()+'ORIGINAL I44 BRIEF (and inheritedI43):\n'+(S/'frozen/frontier/sources/i44_logarithmic_equality_polytopes/brief.txt').read_text()
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
def run(script):
 p=subprocess.run([sys.executable,str(script)],check=True,capture_output=True,text=True,env=env)
 return p.stdout,json.loads(p.stdout)
raw,new=run(E/'check.py')
assert raw==(E/'check-output.json').read_text() and new['status']=='PASS'
_,old=run(R/'frontier/experiments/i44_logarithmic_equality_polytopes/verify.py')
historical=json.loads((E/'i44-replay-output.json').read_text())
def immutable_view(obj):
 if isinstance(obj,dict):return {k:immutable_view(v) for k,v in obj.items() if k!='mutable_input_drift'}
 if isinstance(obj,list):return [immutable_view(x) for x in obj]
 return obj
assert immutable_view(old)==immutable_view(historical)
print(json.dumps({'status':'PASS','scope':'Read-only integrity and exact finite diagnostics; analytic verdicts are in the review, not inferred from these counts.','sealed_artifacts':len(seal['files']),'frozen_inputs':len(frozen),'mutable_ledgers':4,'mutable_input_drift':drift,'inventory_entries':13223,'manuscripts':749,'corpus_files':9340,'selected_pinned_files':len(selected['files']),'source_contracts':len(read('source-contracts.json')),'external_contracts':len(read('external-contracts.json')),'read_passage_records':len(read('read-passages.json')),'responses':len(responses),'successful_responses':sum(bool(r['ok']) for r in responses),'fresh_pinned_responses':sum(r['ok'] and r['file'].startswith('current/fresh/') for r in responses),'independent_exact_assertions':new['assertions'],'i44_replay':old},indent=2,sort_keys=True))
