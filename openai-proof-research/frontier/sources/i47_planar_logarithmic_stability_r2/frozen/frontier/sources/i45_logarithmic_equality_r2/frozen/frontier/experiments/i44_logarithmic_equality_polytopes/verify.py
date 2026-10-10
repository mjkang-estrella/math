#!/usr/bin/env python3
"""Read-only integrity, frozen-ledger, corpus and finite-diagnostic replay. No fetches/writes."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os,re
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i44_logarithmic_equality_polytopes'
E=Path(__file__).resolve().parent
REPORT=R/'frontier/iterations/i44-logarithmic-equality-polytopes.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
MUTABLE=LEDGERS|{'frontier/iterations/iteration44-logarithmic-equality-polytopes-task.json'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads((S/p).read_text())
seal=read('artifact-seal.json')
expected={x['path'] for x in seal['files']}
actual={str(p.relative_to(R)) for base in [S,E] for p in base.rglob('*') if p.is_file() and p!=S/'artifact-seal.json'}|{str(REPORT.relative_to(R))}
assert actual==expected,(actual-expected,expected-actual)
for row in seal['files']:
 p=R/row['path'];assert digest(p)==row['sha256'],row['path']
inv=read('frozen/sources/preprints-tree.json');assert not inv['truncated'];assert len(inv['tree'])==13223
blobs={x['path']:x['sha'] for x in inv['tree'] if x['type']=='blob'}
manuscripts={x['path'].split('/')[1] for x in inv['tree'] if x['path'].startswith('preprints/')};assert len(manuscripts)==749
manifest=read('frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json');assert manifest['pin']==PIN
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
proc=subprocess.run(['rg','--files','--no-ignore',str(C)],check=True,capture_output=True,text=True)
actual={str(Path(x).relative_to(C)) for x in proc.stdout.splitlines()}
expected={x['path'] for x in manifest['files']};assert actual==expected;assert len(actual)==9340
for row in manifest['files']:
 p=C/row['path'];assert p.stat().st_size==row['bytes'];assert digest(p)==row['sha256'];assert blob(p)==row['git_blob']==blobs[row['path']],row['path']
selected=read('selected-manifest.json');assert selected['pin']==PIN
for row in selected['files']:
 p=S/'pinned'/row['path'];assert digest(p)==row['sha256'];assert blob(p)==row['git_blob']==blobs[row['path']]
for row in read('source-contracts.json'):
 text=(S/'pinned'/row['path']).read_text()
 for label in row['labels']:assert '{'+label+'}' in text,(row['path'],label)
for row in read('read-passages.json'):
 p=S/row['path'];assert digest(p)==row['sha256'];lines=p.read_text().splitlines()
 out='\n'.join(f'{i}: {lines[i-1]}' for a,b in row['ranges'] for i in range(a,b+1))+'\n'
 assert (S/row['extract']).read_text()==out,row['path']
responses=read('responses.json')
for row in responses:
 assert digest(S/row['file'])==row['sha256']
 if 'matches_pinned' in row:
  assert row['ok'] and row['matches_pinned']
  assert (S/row['file']).read_bytes()==(S/'pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build'/Path(row['file']).name).read_bytes()
for row in read('versions.json'):
 assert digest(S/row['file'])==row['sha256'];assert (S/row['pdf']).is_file()
assert (S/'literature/centered-v2.pdf').read_bytes()==(S/'literature/centered-lead.pdf').read_bytes()
frozen=read('frozen-inputs.json');assert {x['path'] for x in frozen if x['mutable']}==MUTABLE
drift=[]
for row in frozen:
 p=S/'frozen'/row['path'];assert digest(p)==row['sha256'],row['path'];original=R/row['path']
 if not original.exists() or digest(original)!=row['sha256']:
  if row['mutable']:drift.append(row['path'])
  else:raise AssertionError('immutable original changed: '+row['path'])
# Explicit historical ledger replay uses frozen bytes, never current mutable status text.
ledger=read('frozen-ledger-replay.json');assert {x['path'] for x in ledger}==LEDGERS
for row in ledger:
 p=S/'frozen'/row['path'];assert row['mutable'] and digest(p)==row['frozen_sha256']
 assert row['status_lines']==[[i,l] for i,l in enumerate(p.read_text().splitlines(),1) if re.search(r'6/10|accepted|Accepted|R012',l)]
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
def run(script):
 p=subprocess.run([sys.executable,str(script)],check=True,capture_output=True,text=True,env=env)
 return p.stdout,json.loads(p.stdout)
stdout,checks=run(E/'check.py');assert stdout==(E/'check-output.json').read_text();assert checks['status']=='PASS'
_,old=run(R/'frontier/experiments/i43_convex_isoperimetric_discovery/verify.py')
recorded=json.loads((E/'i43-replay-output.json').read_text())
assert {k:v for k,v in old.items() if k!='mutable_input_drift'}=={k:v for k,v in recorded.items() if k!='mutable_input_drift'}
print(json.dumps({'status':'PASS','scope':'Evidence and finite diagnostics only; analytic deductions require independent parent review.','sealed_artifacts':len(seal['files']),'frozen_inputs':len(frozen),'mutable_ledgers_replayed':len(ledger),'mutable_input_drift':drift,'inventory_entries':len(inv['tree']),'manuscripts':len(manuscripts),'corpus_files':len(expected),'selected_pinned_files':len(selected['files']),'source_contracts':len(read('source-contracts.json')),'responses':len(responses),'successful_responses':sum(x['ok'] for x in responses),'fresh_pinned_responses':sum('matches_pinned' in x for x in responses),'read_passage_records':len(read('read-passages.json')),'exact_assertions':checks['assertions'],'i43_replay':old},indent=2,sort_keys=True))
