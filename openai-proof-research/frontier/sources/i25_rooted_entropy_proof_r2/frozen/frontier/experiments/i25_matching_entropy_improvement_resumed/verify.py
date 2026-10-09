"""Offline byte/provenance verifier; not a mathematical proof checker."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i25_matching_entropy_improvement_resumed';E=R/'frontier/experiments/i25_matching_entropy_improvement_resumed';REPORT=R/'frontier/iterations/i25-matching-entropy-improvement-resumed.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def rel(p):return str(p.relative_to(R))
def metadata(p):
 b=p.read_bytes();return dict(path=rel(p),bytes=len(b),sha256=sha(b))
def inventory():
 return sorted([REPORT]+[p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in [S/'artifact-seal.json',S/'verification.json']],key=rel)
def load(name):return json.loads((S/name).read_text())
if '--seal' in sys.argv:
 (S/'artifact-seal.json').write_text(json.dumps([metadata(p) for p in inventory()],indent=2)+'\n')
errors=[];drift=[];counts={}
def check(ok,msg):
 if not ok:errors.append(msg)
seal=load('artifact-seal.json');check([r['path'] for r in seal]==[rel(p) for p in inventory()],'artifact inventory mismatch')
for row in seal:
 p=R/row['path'];check(p.is_file() and sha(p.read_bytes())==row['sha256'],'artifact '+row['path'])
counts['sealed_artifacts']=len(seal)
original=load('original-checkpoint.json');live=sorted(str(p.relative_to(R)) for d in ['sources','experiments'] for p in (R/f'frontier/{d}/i25_matching_entropy_improvement').rglob('*') if p.is_file());check(sorted(r['path'] for r in original)==live,'original inventory changed')
for row in original:
 p=R/row['path'];check(p.is_file() and sha(p.read_bytes())==row['sha256'],'original changed '+row['path'])
counts['original_files_unchanged']=len(original)
for row in load('inputs.json'):
 p=R/row['snapshot'];check(p.is_file() and sha(p.read_bytes())==row['sha256'],'frozen input '+row['path']);livep=R/row['path'];now=sha(livep.read_bytes()) if livep.is_file() else None
 if now!=row['sha256']:drift.append(dict(path=row['path'],frozen_sha256=row['sha256'],live_sha256=now))
counts['frozen_inputs']=len(load('inputs.json'))
tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());check(not tree['truncated'],'truncated preprint inventory');blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
for row in load('pinned-manifest.json'):
 b=(R/row['local_path']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();check(sha(b)==row['sha256'] and git==row['git_blob']==blobs.get(row['path']),'pinned source '+row['path']);check(row['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+row['path'],'unpinned URL '+row['path'])
counts['pinned_sources']=len(load('pinned-manifest.json'))
for row in load('source-contracts.json'):
 text=(R/row['path']).read_text()[row['start']:row['end']];check(text==row['text'] and sha(text.encode())==row['sha256'],'source contract '+','.join(row['labels']))
counts['source_contracts']=len(load('source-contracts.json'))
for name in ['read-passages.json','primary-passages.json']:
 for row in load(name):
  lines=(R/row['path']).read_text().splitlines(keepends=True);b=''.join(lines[row['start_line']-1:row['end_line']]).encode();check(b.decode()==row['text'] and sha(b)==row['sha256'],'passage '+row['path'])
 counts[name.replace('.json','')]=len(load(name))
for row in load('literature/manifest.json'):
 p=R/row['path'];check(p.is_file() and sha(p.read_bytes())==row['sha256'],'primary bytes '+row['path'])
counts['primary_artifacts']=len(load('literature/manifest.json'))
cm=json.loads((S/'inputs/corpus-manifest.json').read_text())
for row in cm['files']:
 p=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'/row['path'];check(p.is_file() and sha(p.read_bytes())==row['sha256'],'shared corpus '+row['path'])
counts['readonly_corpus_files']=len(cm['files'])
# Index comparison is separately reported: this thread never writes it;
# the parent may legitimately integrate other work concurrently.
idx=load('environment.json')['git_index'];p=R/idx['path'];now=sha(p.read_bytes()) if p.is_file() else None
index_drift=dict(path=idx['path'],initial_sha256=idx['sha256'],live_sha256=now,changed=now!=idx['sha256'])
result=dict(status='PASS' if not errors else 'FAIL',counts=counts,errors=errors,shared_input_drift=drift,git_index_drift=index_drift,scope='Byte/provenance audit only; universal theorem requires separate independent proof and significance review.')
(S/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));sys.exit(bool(errors))
