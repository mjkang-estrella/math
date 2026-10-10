#!/usr/bin/env python3
"""Read-only I51 evidence verifier. No source rewrites, downloads, or seal refresh."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess,os
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i51_hard_moment_quantitative_stability_novelty'
E=R/'frontier/experiments/i51_hard_moment_quantitative_stability_novelty'
REPORT=R/'frontier/reviews/i51-hard-moment-quantitative-stability-novelty.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sha=lambda b:hashlib.sha256(b).hexdigest()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def match(p,r):
 b=p.read_bytes();assert sha(b)==r['sha256'],str(p)
 if 'bytes' in r:assert len(b)==r['bytes'],str(p)
 return b
seal=read(S/'artifact-seal.json');assert seal['pin']==PIN
paths={str(p.relative_to(R)) for root in [S,E] for p in root.rglob('*') if p.is_file()}
paths.add(str(REPORT.relative_to(R)));paths.remove(str((S/'artifact-seal.json').relative_to(R)))
assert paths=={r['path'] for r in seal['files']},'Exact I51 artifact set'
for r in seal['files']:match(R/r['path'],r)
inputs=read(S/'frozen-inputs.json');mutable=[]
for r in inputs:
 match(S/r['copy'],r)
 if r['mutable']:mutable.append(dict(path=r['path'],changed_since_freeze=sha((R/r['path']).read_bytes())!=r['sha256']))
 else:match(R/r['path'],r)
task=read(S/'frozen/frontier/iterations/iteration51-hard-moment-quantitative-stability-novelty-task.json')
assert (S/'brief.txt').read_text()==task['brief']
tree=read(S/'frozen/sources/preprints-tree.json')
assert len(tree['tree'])==13223 and not tree['truncated']
assert len([x for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1])==749
treeblobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
assert read(S/'frozen/sources/upstream.json')['commit']==PIN
manifest=read(S/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
assert manifest['pin']==PIN and len(manifest['files'])==9340
C='frontier/sources/i14_spectral_width_novelty_r3/corpus'
inventory=subprocess.run(['rg','--files','--no-ignore',C],cwd=R,capture_output=True,check=True).stdout.decode().splitlines()
assert {str(Path(p).relative_to(C)) for p in inventory}=={r['path'] for r in manifest['files']}
for r in manifest['files']:
 b=match(R/C/r['path'],r);assert blob(b)==r['git_blob']==treeblobs[r['path']]
A=S/'frozen/frontier/sources/i49_hard_moment_quantitative_stability'
selected=read(A/'selected-manifest.json')
assert selected['pin']==PIN and len(selected['files'])==12
for r in selected['files']:
 b=match(A/'pinned'/r['path'],r);assert blob(b)==treeblobs[r['path']]
 assert b==(R/C/r['path']).read_bytes()
for name in ['density','tensor']:
 target=A/f'pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/{name}.tex'
 assert target.read_bytes()==(S/f'primary/{name}-fresh.tex').read_bytes()
responses=read(S/'responses.json')+read(S/'extra-responses.json');pdfs=0
for r in responses:
 p=S/r['file'];b=match(p,r)
 if b.startswith(b'%PDF'):
  run=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
  assert run.stdout==p.with_suffix('.txt').read_bytes(),str(p)
  assert r['pdftotext_returncode']==0;pdfs+=1
for r in read(S/'versions.json'):
 match(S/r['file'],r);lines=(S/r['file']).read_text().splitlines()
 for line in r['version_lines']:assert line in lines
passages=read(S/'read-passages.json')
for r in passages:
 b=(S/r['source']).read_bytes();assert sha(b)==r['source_sha256']
 extract=b''.join(b.splitlines(keepends=True)[r['first_line']-1:r['last_line']])
 assert extract==match(S/r['extract'],r)
for r in read(S/'corpus-search.json'):
 run=subprocess.run(['rg','--no-ignore','-n','-i',r['pattern'],C],cwd=R,capture_output=True)
 assert run.returncode==r['returncode']
 assert Counter(run.stdout.splitlines())==Counter((S/r['output']).read_bytes().splitlines())
 assert len(run.stdout.splitlines())==r['lines']
network=read(S/'network-summary.json')
assert network['responses']==len(responses)==31 and network['pdfs']==pdfs==19
assert network['successes']==sum(r['ok'] for r in responses)==31 and network['failures']==0
run=subprocess.run([sys.executable,'-B',str(E/'check.py')],cwd=R,capture_output=True,check=True)
assert run.stdout==(E/'check-output.json').read_bytes()
checks=json.loads(run.stdout);assert checks['status']=='PASS' and checks['exact_assertions']==309

# Reproduce ONLY the known author rg-order comparison adjustment in memory.
# This is explicitly a modified replay, never labeled an unmodified PASS.
rec=read(S/'i49-normalized-replay.json')
p=R/'frontier/experiments/i49_hard_moment_quantitative_stability/verify.py'
before=p.read_bytes();assert sha(before)==rec['source_sha256']
src=before.decode();assert src.count(rec['original'])==1
assert rec['original']=="assert run.stdout==(S/r['output']).read_bytes()"
assert rec['replacement']=="assert sorted(run.stdout.splitlines())==sorted((S/r['output']).read_bytes().splitlines())"
assert rec['returncode']==0 and not rec['disk_files_modified']
run=subprocess.run([sys.executable,'-B','-c','__file__='+repr(str(p))+'\n'+src.replace(rec['original'],rec['replacement'])],cwd=R,capture_output=True,check=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
author=json.loads(run.stdout);assert author['status']=='PASS'
assert p.read_bytes()==before
for key in ['I49_sealed_artifacts','frozen_inputs','prior_seals','prior_artifact_hash_checks','tree_entries','manuscripts','corpus_files_verified','selected_pinned_files','primary_responses','PDF_text_replays','read_records','exact_assertions']:
 assert author[key]==json.loads(rec['stdout'])[key]
print(json.dumps(dict(status='PASS',pin=PIN,I51_sealed_artifacts=len(seal['files']),frozen_inputs=len(inputs),read_records=len(passages),primary_responses=len(responses),PDF_text_replays=pdfs,exact_assertions=checks['exact_assertions'],tree_entries=13223,manuscripts=749,corpus_files_verified=9340,
 I49_replay='PASS with single in-memory line-multiset normalization; not unmodified verifier',I49_sealed_artifacts=author['I49_sealed_artifacts'],prior_seals=author['prior_seals'],prior_artifact_hash_checks=author['prior_artifact_hash_checks'],I49_exact_assertions=author['exact_assertions'],mutable_observations=mutable,
 scope='Integrity and finite diagnostics only; no original-proof PASS, acceptance, or priority certification'),indent=2))
