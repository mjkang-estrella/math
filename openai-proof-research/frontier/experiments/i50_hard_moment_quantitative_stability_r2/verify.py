#!/usr/bin/env python3
"""Read-only I50 seal, complete corpus, source, and diagnostic replay."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i50_hard_moment_quantitative_stability_r2';E=R/'frontier/experiments/i50_hard_moment_quantitative_stability_r2';REPORT=R/'frontier/reviews/i50-hard-moment-quantitative-stability-r2.md';PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def match(p,r):
 b=p.read_bytes();assert sha(b)==r['sha256'],str(p)
 if 'bytes' in r:assert len(b)==r['bytes'],str(p)
 return b
seal=read(S/'artifact-seal.json');assert seal['pin']==PIN
paths={str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file()};paths.add(str(REPORT.relative_to(R)));paths.remove(str((S/'artifact-seal.json').relative_to(R)))
assert paths=={r['path'] for r in seal['files']},'exact I50 artifact set'
for r in seal['files']:match(R/r['path'],r)
mutable=[];inputs=read(S/'frozen-inputs.json')
for r in inputs:
 match(S/'frozen'/r['path'],r)
 if r['mutable']:mutable.append({'path':r['path'],'changed_since_I50_freeze':sha((R/r['path']).read_bytes())!=r['sha256']})
 else:match(R/r['path'],r)
task=read(S/'frozen/frontier/iterations/iteration50-hard-moment-quantitative-stability-r2-task.json');assert (S/'brief.txt').read_text()==task['brief']
tree=read(S/'frozen/sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'];assert len([x for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1])==749
treeblobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'};assert read(S/'frozen/sources/upstream.json')['commit']==PIN
corpusrel='frontier/sources/i14_spectral_width_novelty_r3/corpus';corpus=R/corpusrel
manifest=read(S/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json');assert manifest['pin']==PIN and len(manifest['files'])==9340
inventory=subprocess.run(['rg','--files','--no-ignore',corpusrel],cwd=R,capture_output=True,check=True).stdout.decode().splitlines();assert len(inventory)==9340
assert {str(Path(p).relative_to(corpusrel)) for p in inventory}=={r['path'] for r in manifest['files']}
for r in manifest['files']:
 b=match(corpus/r['path'],r);assert blob(b)==r['git_blob']==treeblobs[r['path']]
old=R/'frontier/sources/i49_hard_moment_quantitative_stability';oldf=S/'frozen/frontier/sources/i49_hard_moment_quantitative_stability'
selected=read(oldf/'selected-manifest.json');assert selected['pin']==PIN
for r in selected['files']:
 b=match(oldf/'pinned'/r['path'],r);assert b==(corpus/r['path']).read_bytes();assert blob(b)==treeblobs[r['path']]
prior_seals=read(oldf/'prior-seals.json');prior_paths=[r['path'] for r in prior_seals]+[str((old/'artifact-seal.json').relative_to(R))];prior_count=0
for path in prior_paths:
 b=(R/path).read_bytes();assert b==(S/'frozen'/path).read_bytes();data=json.loads(b);assert data['pin']==PIN
 for r in data['files']:match(R/r['path'],r);prior_count+=1
responses=read(S/'responses.json');pdfs=0
for r in responses:
 p=S/r['file'];b=match(p,r);assert r['ok'] and r['status']==200
 assert b==(oldf/r['file']).read_bytes()
 if b.startswith(b'%PDF'):
  run=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True);assert run.stdout==p.with_suffix('.txt').read_bytes();pdfs+=1
for r in read(S/'versions.json'):
 b=match(S/r['source'],r)
 for line in r['literal_version_lines']:assert line in b.decode().splitlines()
passages=read(S/'read-passages.json')
for r in passages:
 b=(S/r['source']).read_bytes();assert sha(b)==r['source_sha256'];ex=b''.join(b.splitlines(keepends=True)[r['first_line']-1:r['last_line']]);assert ex==match(S/r['extract'],r)
searches=read(S/'corpus-search.json')
for r in searches:
 b=match(S/r['output'],r);run=subprocess.run(['rg','--no-ignore','-n','-i',r['pattern'],corpusrel],cwd=R,capture_output=True)
 assert run.returncode==r['returncode'];assert sorted(run.stdout.splitlines())==sorted(b.splitlines()),'corpus line multiset differs'
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
run=subprocess.run([sys.executable,str(E/'check.py')],cwd=R,capture_output=True,env=env,check=True);assert run.stdout==(E/'check-output.json').read_bytes();diag=json.loads(run.stdout);assert diag['exact_assertions']==310
run=subprocess.run([sys.executable,str(E/'replay_i49.py')],cwd=R,capture_output=True,env=env,check=True);replay=json.loads(run.stdout);frozen_replay=read(E/'i49-replay-output.json')
for k in ['kind','source_sha256','original','replacement','disk_source_unchanged','error']:assert replay[k]==frozen_replay[k]
assert replay['error'] is None and replay['disk_source_unchanged']
actual=json.loads(replay['stdout']);previous=json.loads(frozen_replay['stdout'])
for k,v in actual.items():
 if k!='mutable_observations':assert v==previous[k]
parent=read(S/'frozen/frontier/experiments/i49-parent-verification.json');assert parent['initial_verifier_attempt']['returncode']==1 and parent['unmodified_verifier_retry']['returncode']==0
print(json.dumps({'status':'PASS','scope':'Read-only byte integrity and exact diagnostics; analytic verdict is in the report, not inferred from these checks','pin':PIN,'I50_sealed_artifacts':len(seal['files']),'frozen_inputs':len(inputs),'read_records':len(passages),'fresh_primary_responses':len(responses),'PDF_text_replays':pdfs,'tree_entries':13223,'manuscripts':749,'corpus_files':9340,'selected_pins':len(selected['files']),'corpus_search_line_multisets':len(searches),'unchanged_prior_seals':len(prior_paths),'prior_artifact_hash_checks':prior_count,'independent_exact_assertions':diag['exact_assertions'],'I49_replay':'PASS with one explicitly recorded in-memory line-multiset normalization; not vanilla','I49_parent_initial_vanilla':'FAILED as preserved','I50_mutable_observations':mutable,'I49_mutable_observations':actual['mutable_observations']},indent=2))
