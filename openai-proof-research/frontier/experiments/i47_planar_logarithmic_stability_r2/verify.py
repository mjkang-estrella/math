#!/usr/bin/env python3
"""Read-only evidence replay. No downloads, edits, bytecode, or seal refresh."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib, json, os, subprocess

R = Path(__file__).resolve().parents[3]
S = R / 'frontier/sources/i47_planar_logarithmic_stability_r2'
E = Path(__file__).resolve().parent
REPORT = R / 'frontier/reviews/i47-planar-logarithmic-stability-r2.md'
I46 = S / 'frozen/frontier/sources/i46_quantitative_logarithmic_stability'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE = {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md',
           'frontier/iterations/iteration47-planar-logarithmic-stability-r2-task.json'}

def read(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def blob(p):
    b=p.read_bytes()
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

seal=read(S/'artifact-seal.json')
ckset={str(p.relative_to(R)) for base in (S,E) for p in base.rglob('*')
       if p.is_file() and p != S/'artifact-seal.json'} | {str(REPORT.relative_to(R))}
assert ckset=={x['path'] for x in seal['files']}
assert seal['pin']==PIN
for row in seal['files']:
    p=R/row['path']
    assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row['path']

inputs=read(S/'frozen-inputs.json')
assert {x['path'] for x in inputs if x['mutable']}==MUTABLE
drift=[]
for row in inputs:
    frozen=S/'frozen'/row['path'];live=R/row['path']
    assert sha(frozen)==row['sha256'] and frozen.stat().st_size==row['bytes'],row['path']
    if not live.is_file() or sha(live)!=row['sha256']:
        assert row['mutable'],'Immutable dependency changed: '+row['path']
        drift.append(row['path'])
task=read(S/'frozen/frontier/iterations/iteration47-planar-logarithmic-stability-r2-task.json')
assert (S/'brief.txt').read_text()==task['brief']

historical=[]
for tag,folder in [('i43','i43_convex_isoperimetric_discovery'),
                   ('i44','i44_logarithmic_equality_polytopes'),
                   ('i45','i45_logarithmic_equality_r2'),
                   ('i46','i46_quantitative_logarithmic_stability')]:
    rel=f'frontier/sources/{folder}/artifact-seal.json'
    frozen=S/'frozen'/rel
    assert frozen.read_bytes()==(R/rel).read_bytes()
    prior=read(frozen)
    for row in prior['files']:
        assert sha(R/row['path'])==row['sha256'],row['path']
        assert sha(S/'frozen'/row['path'])==row['sha256'],row['path']
    historical.append({'tag':tag,'unchanged_artifacts':len(prior['files'])})

tree=read(S/'frozen/sources/preprints-tree.json')
assert not tree['truncated'] and len(tree['tree'])==13223
blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
papers={x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')}
assert len(papers)==749
manifest=read(I46/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
assert manifest['pin']==PIN
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
listed=subprocess.run(['rg','--files','--no-ignore',str(C)],check=True,capture_output=True,text=True).stdout.splitlines()
assert {str(Path(p).relative_to(C)) for p in listed}=={x['path'] for x in manifest['files']}
assert len(listed)==9340
for row in manifest['files']:
    p=C/row['path']
    assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row['path']
    assert blob(p)==row['git_blob']==blobs[row['path']],row['path']
selected=read(I46/'inherited-selected-manifest.json')
assert selected['pin']==PIN and len(selected['files'])==12
for row in selected['files']:
    p=I46/'pinned'/row['path']
    assert sha(p)==row['sha256'] and blob(p)==row['git_blob']==blobs[row['path']]
for row in read(S/'source-contracts.json'):
    text=(S/row['frozen_source']).read_text()
    assert all('{'+label+'}' in text for label in row['labels'])

responses=read(S/'responses.json')
for row in responses:
    assert sha(S/row['file'])==row['sha256'] and (S/row['file']).stat().st_size==row['bytes']
for row in read(S/'fresh-bindings.json'):
    assert sha(S/row['fresh'])==sha(S/row['inherited'])==row['sha256']
for row in read(S/'versions.json'):
    p=S/row['path'];assert sha(p)==row['sha256']
    text=p.read_text();assert row['canonical_version_url'] in text
    assert all(x in text for x in row['submission_lines'])
passages=read(S/'read-passages.json')
for row in passages:
    p=S/row['path'];assert sha(p)==row['sha256']
    lines=p.read_text().splitlines()
    extract='\n'.join(f'{i}: {lines[i-1]}' for a,b in row['ranges'] for i in range(a,b+1))+'\n'
    assert extract==(S/row['extract']).read_text(),row['path']

env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
run=subprocess.run([sys.executable,str(E/'check.py')],check=True,capture_output=True,text=True,env=env)
assert run.stdout==(E/'check-output.json').read_text()
diagnostic=json.loads(run.stdout)
assert diagnostic['status']=='PASS' and diagnostic['exact_assertions']==1049
old=subprocess.run([sys.executable,str(R/'frontier/experiments/i46_quantitative_logarithmic_stability/verify.py')],check=True,capture_output=True,text=True,env=env)
replay=json.loads(old.stdout);saved=read(E/'i46-replay-output.json')
assert {k:v for k,v in replay.items() if k!='mutable_input_drift'}=={k:v for k,v in saved.items() if k!='mutable_input_drift'}
assert replay['status']=='PASS'
print(json.dumps({'status':'PASS','scope':'Read-only provenance and finite exact checks, not a mechanical analytic or significance certificate.',
 'sealed_artifacts':len(seal['files']),'frozen_inputs':len(inputs),'mutable_shared_ledgers':4,
 'mutable_orchestration_records':1,'mutable_input_drift':drift,'historical_seals':historical,
 'tree_entries':13223,'manuscripts':749,'corpus_files':9340,'selected_pins':12,
 'fresh_responses':len(responses),'successful_fresh_responses':sum(x['ok'] for x in responses),
 'read_passage_records':len(passages),'exact_assertions':diagnostic['exact_assertions'],
 'genuine_zonotope_cases':diagnostic['genuine_zonotope_cases'],
 'i46_replay':{'status':replay['status'],'exact_assertions':replay['exact_assertions'],
               'mutable_input_drift':replay['mutable_input_drift']},
 'analytic_review_verdict':'P10 PASS ORIGINAL WITHOUT REPAIRS; construction A partial/conditional budgets only; higher-dimensional target unproved; no significance or acceptance determination.'},indent=2,sort_keys=True))
