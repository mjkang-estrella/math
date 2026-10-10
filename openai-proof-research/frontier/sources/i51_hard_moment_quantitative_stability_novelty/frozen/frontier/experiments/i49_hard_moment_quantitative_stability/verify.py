#!/usr/bin/env python3
"""Read-only I49 verification. Integrity and finite diagnostics are not proof review."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i49_hard_moment_quantitative_stability'
E=R/'frontier/experiments/i49_hard_moment_quantitative_stability'
REPORT=R/'frontier/iterations/i49-hard-moment-quantitative-stability.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def match(p,r):
 b=p.read_bytes();assert sha(b)==r['sha256'],str(p)
 if 'bytes' in r:assert len(b)==r['bytes'],str(p)
 return b
seal=read(S/'artifact-seal.json')
assert seal['pin']==PIN
paths={str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file()}
paths.add(str(REPORT.relative_to(R)));paths.remove(str((S/'artifact-seal.json').relative_to(R)))
assert paths=={r['path'] for r in seal['files']},'I49 exact artifact set'
for r in seal['files']:match(R/r['path'],r)
inputs=read(S/'frozen-inputs.json');mutable=[]
for r in inputs:
 match(S/'frozen'/r['path'],r)
 if r['mutable']:
  mutable.append({'path':r['path'],'changed_since_freeze':sha((R/r['path']).read_bytes())!=r['sha256']})
 else:match(R/r['path'],r)
task=read(S/'frozen/frontier/iterations/iteration49-hard-moment-quantitative-stability-task.json')
assert (S/'brief.txt').read_text().rstrip('\n')==task['brief'].rstrip('\n')
old=read(S/'prior-seals.json');oldcount=0
for r in old:
 match(R/r['path'],r);match(S/'frozen'/r['path'],r)
 data=read(R/r['path']);assert data['pin']==PIN
 assert len(data['files'])==r['artifacts']
 for item in data['files']:match(R/item['path'],item);oldcount+=1
tree=read(S/'frozen/sources/preprints-tree.json')
assert len(tree['tree'])==13223 and not tree['truncated']
assert len([x for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1])==749
treeblobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
assert read(S/'frozen/sources/upstream.json')['commit']==PIN
manifest=read(S/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
assert manifest['pin']==PIN and len(manifest['files'])==9340
corpusrel='frontier/sources/i14_spectral_width_novelty_r3/corpus'
corpus=R/corpusrel
inventory=subprocess.run(['rg','--files','--no-ignore',corpusrel],cwd=R,capture_output=True,check=True).stdout.decode().splitlines()
assert {str(Path(p).relative_to(corpusrel)) for p in inventory}=={r['path'] for r in manifest['files']}
for r in manifest['files']:
 b=match(corpus/r['path'],r);assert blob(b)==r['git_blob']==treeblobs[r['path']]
selected=read(S/'selected-manifest.json');assert selected['pin']==PIN and len(selected['files'])==12
for r in selected['files']:
 b=match(S/'pinned'/r['path'],r);assert blob(b)==r['git_blob']==treeblobs[r['path']]
 assert b==(corpus/r['path']).read_bytes()
for name in ['tensor','density']:
 assert (S/f'primary/{name}-fresh.tex').read_bytes()==(S/f'pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/{name}.tex').read_bytes()
responses=read(S/'responses.json');pdfs=0
for r in responses:
 p=S/r['file'];b=match(p,r)
 if b.startswith(b'%PDF'):
  run=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
  assert run.stdout==p.with_suffix('.txt').read_bytes(),str(p)
  assert r['pdftotext_returncode']==0
  pdfs+=1
versions=read(S/'versions.json')
for r in versions:
 p=S/r['file'];match(p,r)
 for line in r.get('version_lines',[]):assert line in p.read_text().splitlines()
 for line in r.get('arxiv_header',[]):assert line in p.read_text()
passages=read(S/'read-passages.json')
for r in passages:
 b=(S/r['source']).read_bytes();assert sha(b)==r['source_sha256']
 extract=b''.join(b.splitlines(keepends=True)[r['first_line']-1:r['last_line']])
 assert extract==match(S/r['extract'],r)
for r in read(S/'runtime-inputs.json'):
 assert match(S/r['copy'],r)==match(R/r['path'],r)
for r in read(S/'corpus-search.json'):
 run=subprocess.run(['rg','--no-ignore','-n','-i',r['pattern'],corpusrel],cwd=R,capture_output=True)
 assert run.returncode==r['returncode']
 assert run.stdout==(S/r['output']).read_bytes()
network=read(S/'network-summary.json')
assert network['responses']==len(responses)
assert network['successes']==sum(r['ok'] for r in responses)
assert network['failures']==sum(not r['ok'] for r in responses)
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
run=subprocess.run([sys.executable,str(E/'check.py')],cwd=R,capture_output=True,env=env,check=True)
assert run.stdout==(E/'check-output.json').read_bytes()
diagnostics=json.loads(run.stdout);assert diagnostics['status']=='PASS'
print(json.dumps({'status':'PASS','pin':PIN,'I49_sealed_artifacts':len(seal['files']),
 'frozen_inputs':len(inputs),'prior_seals':len(old),'prior_artifact_hash_checks':oldcount,
 'tree_entries':13223,'manuscripts':749,'corpus_files_verified':len(manifest['files']),
 'selected_pinned_files':12,'primary_responses':len(responses),'PDF_text_replays':pdfs,
 'read_records':len(passages),'exact_assertions':diagnostics['exact_assertions'],
 'mutable_observations':mutable,
 'scope':'Read-only byte integrity and exact diagnostic replay; no analytic or significance approval'},indent=2))
