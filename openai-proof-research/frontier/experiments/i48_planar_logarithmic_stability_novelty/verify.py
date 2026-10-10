#!/usr/bin/env python3
"""Read-only evidence verification: no downloads, writes, seal refresh, or bytecode."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i48_planar_logarithmic_stability_novelty';E=Path(__file__).resolve().parent
REPORT=R/'frontier/reviews/i48-planar-logarithmic-stability-novelty.md';PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
 b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(rel):return json.loads((S/rel).read_text())
seal=read('artifact-seal.json');assert seal['pin']==PIN
actual={str(p.relative_to(R)) for base in (S,E) for p in base.rglob('*') if p.is_file() and p!=S/'artifact-seal.json'}|{str(REPORT.relative_to(R))}
assert actual=={row['path'] for row in seal['files']}
for row in seal['files']:assert sha(R/row['path'])==row['sha256'] and (R/row['path']).stat().st_size==row['bytes'],row['path']
frozen=read('frozen-inputs.json');assert {x['path'] for x in frozen if x['mutable']}==MUTABLE
drift=[]
for row in frozen:
 assert sha(S/'frozen'/row['path'])==row['sha256']
 if not (R/row['path']).exists() or sha(R/row['path'])!=row['sha256']:
  assert row['mutable'],'Immutable changed: '+row['path'];drift.append(row['path'])
assert (S/'brief.txt').read_text()==(S/'brief-prefix.txt').read_text()+(S/'frozen/frontier/sources/i46_quantitative_logarithmic_stability/brief.txt').read_text()
history=[]
for row in read('prior-seals.json'):
 assert sha(R/row['path'])==sha(S/'frozen'/row['path'])==row['sha256']
 old=json.loads((R/row['path']).read_text());assert len(old['files'])==row['artifacts']
 for x in old['files']:assert sha(R/x['path'])==x['sha256'],x['path']
 history.append({'seal':row['path'],'unchanged_artifacts':len(old['files'])})
inv=read('frozen/sources/preprints-tree.json');assert not inv['truncated'] and len(inv['tree'])==13223
blobs={x['path']:x['sha'] for x in inv['tree'] if x['type']=='blob'}
assert len({x['path'].split('/')[1] for x in inv['tree'] if x['path'].startswith('preprints/')})==749
manifest=read('frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json');assert manifest['pin']==PIN
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
listed=subprocess.run(['rg','--files','--no-ignore',str(C)],check=True,capture_output=True,text=True).stdout.splitlines()
assert {str(Path(p).relative_to(C)) for p in listed}=={x['path'] for x in manifest['files']};assert len(listed)==9340
for x in manifest['files']:
 p=C/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'];assert blob(p)==x['git_blob']==blobs[x['path']]
for row in read('corpus-search.json'):
 run=subprocess.run(['rg','--no-ignore','-n','-i',row['pattern'],str(C)],capture_output=True,text=True)
 assert run.returncode==row['returncode'];assert sorted(run.stdout.splitlines())==sorted((S/row['output']).read_text().splitlines())
sel=read('frozen/frontier/sources/i46_quantitative_logarithmic_stability/inherited-selected-manifest.json');assert sel['pin']==PIN
for row in sel['files']:
 p=S/'pinned'/row['path'];assert sha(p)==row['sha256'];assert blob(p)==row['git_blob']==blobs[row['path']]
for row in read('pinned-contracts.json'):
 text=(S/'pinned'/row['path']).read_text()
 for label in row['labels']:assert '{'+label+'}' in text
responses=read('responses.json')
for row in responses:
 p=S/row['file'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
 if row.get('pdftotext_returncode')==0:
  run=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
  assert run.stdout==p.with_suffix('.txt').read_bytes(),row['file']
assert (S/'primary/pinned-reduction.tex').read_bytes()==(S/'pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/reduction.tex').read_bytes()
for row in read('versions.json'):
 p=S/row['file'];assert sha(p)==row['sha256'];t=p.read_text();assert row['canonical_version_url'] in t
 for line in row['submission_lines']:assert line in t
for row in read('read-passages.json'):
 p=S/row['path'];assert sha(p)==row['sha256'];lines=p.read_text().splitlines()
 excerpt='\n'.join(f'{i}: {lines[i-1]}' for a,b in row['ranges'] for i in range(a,b+1))+'\n'
 assert excerpt==(S/row['extract']).read_text()
for row in read('external-contracts.json'):assert sha(S/row['file'])==row['sha256']
run=subprocess.run([sys.executable,str(E/'check.py')],capture_output=True,text=True,check=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
assert run.stdout==(E/'check-output.json').read_text();diagnostic=json.loads(run.stdout);assert diagnostic['status']=='PASS' and diagnostic['exact_assertions']==1830
print(json.dumps({'status':'PASS','scope':'Evidence integrity and finite exact diagnostics; not I47 original-proof approval or worldwide novelty certification','sealed_artifacts':len(seal['files']),'frozen_inputs':len(frozen),'mutable_shared_ledgers':4,'mutable_drift':drift,'historical_seals':history,'tree_entries':13223,'manuscripts':749,'corpus_files':len(listed),'corpus_searches':len(read('corpus-search.json')),'selected_pinned_files':len(sel['files']),'fresh_responses':len(responses),'successful_fresh_responses':sum(x['ok'] for x in responses),'retained_failed_responses':sum(not x['ok'] for x in responses),'version_records':len(read('versions.json')),'read_passages':len(read('read-passages.json')),'exact_assertions':diagnostic['exact_assertions'],'sine_graph_cases':diagnostic['sine_graph_cases'],'contribution_verdict':'TECHNICAL ONLY; no exact duplicate claim','original_proof_status':'I47 not read; contribution disposition conditional on separate audit'},indent=2,sort_keys=True))
