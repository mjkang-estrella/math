"""Offline integrity/reproduction verifier; writes only R3 verification.json and R3 diagnostics.json.
Run --seal once after finalizing review-owned artifacts; plain invocation only verifies.
This verifies evidence integrity, not mathematical truth or exhaustive priority.
"""
from pathlib import Path
import json,hashlib,subprocess,sys,os
ROOT=Path(__file__).resolve().parents[3];os.chdir(ROOT)
S=Path('frontier/sources/i25_rooted_entropy_novelty_r3');E=Path('frontier/experiments/i25_rooted_entropy_novelty_r3')
R=Path('frontier/reviews/i25-rooted-entropy-novelty-r3.md')
def sha(b):return hashlib.sha256(b).hexdigest()
def get(p):return json.loads(Path(p).read_text())
def entry(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
def write(p,v):p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
exclude={S/'artifact-seal.json',S/'verification.json'}
if '--seal' in sys.argv:
 files=sorted({R}|{p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in exclude})
 write(S/'artifact-seal.json',[entry(p) for p in files])
errors=[];counts={};drift=[]
def check(r,path=None):
 p=Path(path or r['path'])
 if not p.exists():errors.append('missing '+str(p));return
 b=p.read_bytes()
 if sha(b)!=r['sha256']:errors.append('sha256 '+str(p))
 if 'bytes'in r and len(b)!=r['bytes']:errors.append('size '+str(p))
seal=get(S/'artifact-seal.json')
for r in seal:check(r)
counts['sealed_artifacts']=len(seal)
actual={str(p) for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in exclude}|{str(R)}
if actual!={r['path']for r in seal}:errors.append('review inventory differs from seal')
ins=get(S/'inputs.json')
for r in ins:
 check(r,r['frozen'])
 p=Path(r['path'])
 if not p.exists() or sha(p.read_bytes())!=r['sha256']:drift.append(dict(path=r['path'],frozen=r['sha256'],current=sha(p.read_bytes())if p.exists()else None))
counts['frozen_inputs']=len(ins)
tree=get(S/'frozen/sources/preprints-tree.json')
if tree.get('truncated'):errors.append('truncated inventory')
blobs={r['path']:r['sha']for r in tree['tree']if r['type']=='blob'}
pins=get(S/'pinned-manifest.json')
for r in pins:
 check(r,r['local_path']);b=Path(r['local_path']).read_bytes()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if blob!=r['git_blob']or blobs.get(r['path'])!=blob:errors.append('git blob '+r['path'])
 if 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'not in r['url']:errors.append('wrong pin '+r['path'])
counts['pinned_sources']=len(pins)
for fn in ['source-contracts.json','read-passages.json']:
 rows=get(S/fn)
 for r in rows:
  b=Path(r['path']).read_bytes();t=b.decode()
  if fn=='source-contracts.json':
   if r['text']not in t or sha(r['text'].encode())!=r['sha256']:errors.append('contract '+r['path'])
  else:
   excerpt=''.join(t.splitlines(keepends=True)[r['start_line']-1:r['end_line']])
   if sha(b)!=r['file_sha256']or excerpt!=r['text']or sha(excerpt.encode())!=r['excerpt_sha256']:errors.append('passage '+r['path'])
 counts[fn.removesuffix('.json').replace('-','_')]=len(rows)
literature=[]
for fn in ['manifest.json','extra-manifest.json']:
 literature+=get(S/'literature'/fn)
# One URL was retrieved twice; retain both logs, verify bytes against the latest retrieval.
last={}
for r in literature:
 if 'path'in r:last[r['path']]=r
for r in last.values():
 check(r)
 if 'text_path'in r:check(dict(sha256=r['text_sha256']),r['text_path'])
counts['retrieved_byte_artifacts']=len(last)
counts['parsed_primary_texts']=sum('text_path'in r for r in last.values())
for fn,key in [('artifact-seal.json','resumed_author_artifacts'),('original-checkpoint.json','original_unchanged_files')]:
 rows=get(S/'frozen/frontier/sources/i25_matching_entropy_improvement_resumed'/fn)
 for r in rows:check(r)
 counts[key]=len(rows)
# Independently recheck the full cache without writing or copying it.
cache=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
cm=get(cache.parent/'corpus-manifest.json')
for r in cm['files']:check(r,cache/r['path'])
counts['readonly_cache_files']=len(cm['files'])
before=(E/'diagnostics.json').read_bytes()
result=subprocess.run([sys.executable,str(E/'diagnostics.py')],capture_output=True,text=True)
if result.returncode:errors.append('diagnostics failed '+result.stderr)
if before!=(E/'diagnostics.json').read_bytes():errors.append('diagnostics reproduction changed bytes')
diagnostics=get(E/'diagnostics.json')
index=Path(subprocess.check_output(['git','rev-parse','--git-path','index'],text=True).strip())
current_index=sha(index.read_bytes())
baseline=get(S/'baseline.json')
index_drift=current_index!=baseline['git_index_sha256']
# Critical candidate drift is a failure; shared index/ledger drift is separately disclosed.
critical=[r for r in drift if r['path'].endswith('i25-matching-entropy-improvement-resumed.md')]
errors+=['critical candidate drift'for r in critical]
v=dict(status='PASS'if not errors else'FAIL',purpose='Evidence integrity and exact diagnostic reproduction, not a proof/priority verdict',
counts=counts,diagnostics={k:diagnostics[k]for k in ['status','charged_edge_checks','trace_checks']},
errors=errors,shared_input_drift=drift,git_index_drift=dict(changed=index_drift,baseline=baseline['git_index_sha256'],current=current_index),
candidate_sha256=sha(Path('frontier/iterations/i25-matching-entropy-improvement-resumed.md').read_bytes()),review_sha256=sha(R.read_bytes()),
artifact_seal_sha256=sha((S/'artifact-seal.json').read_bytes()))
write(S/'verification.json',v);print(json.dumps(v,indent=2));sys.exit(bool(errors))
