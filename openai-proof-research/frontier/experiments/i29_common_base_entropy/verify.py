"""Offline evidence verifier. Optional reproduction writes only assigned I29 outputs."""
from pathlib import Path
import hashlib,json,subprocess,sys,os,datetime
S=Path('frontier/sources/i29_common_base_entropy');E=Path('frontier/experiments/i29_common_base_entropy');REPORT=Path('frontier/iterations/i29-common-base-entropy.md')
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def check(p,h,size=None):
 b=Path(p).read_bytes();assert sha(b)==h,str(p)+' SHA mismatch'
 if size is not None:assert len(b)==size,str(p)+' size mismatch'
 return b
out={'status':'RUNNING','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 inputs=read(S/'inputs.json');drift=[]
 for r in inputs:
  check(r['frozen'],r['sha256'],r['bytes'])
  if not Path(r['path']).exists() or sha(Path(r['path']).read_bytes())!=r['sha256']:drift.append(r['path'])
 tree=read(S/'inputs/sources/preprints-tree.json');assert not tree['truncated'];idx={r['path']:r for r in tree['tree']};roots={p.split('/')[1] for p in idx if p.startswith('preprints/')};assert len(roots)==749
 for r in read(S/'pinned-manifest.json'):
  b=check(r['local'],r['sha256'],r['bytes']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==r['git_blob']==idx[r['path']]['sha']
 corpus=read(S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json');assert len(corpus['files'])==9340
 for r in corpus['files']:check(Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')/r['path'],r['sha256'],r['bytes'])
 for r in read(S/'literature/manifest.json'):
  b=check(r['path'],r['sha256'],r['bytes'])
  if r['path'].endswith('.pdf'):assert b.startswith(b'%PDF-')
  if 'text_path' in r:check(r['text_path'],r['text_sha256'])
 for r in read(S/'read-passages.json'):
  txt=''.join(Path(r['path']).read_text().splitlines(keepends=True)[r['first_line']-1:r['last_line']]);assert txt==r['text'] and sha(txt.encode())==r['sha256']
 for r in read(S/'source-contracts.json'):
  txt=Path(r['path']).read_text();assert r['text'] in txt and sha(r['text'].encode())==r['sha256']
 for r in read(S/'current-versions.json'):check(r['path'],r['sha256'])
 if '--reproduce' in sys.argv:
  before={p:sha(p.read_bytes()) for p in [E/'results.json',E/'boundary-results.json']}
  for f in ['diagnostics.py','boundary_diagnostics.py']:
   z=subprocess.run([sys.executable,str(E/f)],env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True);assert z.returncode==0,z.stderr
  assert all(sha(p.read_bytes())==h for p,h in before.items()),'Reproduced diagnostics differ'
  out['diagnostics_reproduced_byte_identically']=True
 seal=read(S/'artifact-seal.json');excluded={str(S/'artifact-seal.json'),str(S/'verification.json')};actual={str(p) for root in [S,E] for p in root.rglob('*') if p.is_file() and str(p) not in excluded}|{str(REPORT)}
 assert actual=={r['path'] for r in seal['files']},'Seal file set differs'
 for r in seal['files']:check(r['path'],r['sha256'],r['bytes'])
 git={cmd:subprocess.check_output(cmd.split(),text=True) for cmd in ['git rev-parse HEAD','git status --porcelain','git diff --cached --stat']}
 old=read(S/'git-start.json');out.update(status='PASS',frozen_inputs=len(inputs),pinned_files=len(read(S/'pinned-manifest.json')),inventory_manuscripts=749,read_only_cache_files=9340,read_passages=len(read(S/'read-passages.json')),source_statement_contracts=len(read(S/'source-contracts.json')),sealed_files=len(seal['files']),live_input_drift=drift,git_changed_fields=[k for k in old if old[k]!=git[k]],git_final=git)
 out['scope_note']='Live shared input or Git drift is reported, not attributed to I29. This script does not stage, commit, edit shared data, access network, or audit stipulated proofs.'
except Exception as e:
 out.update(status='FAIL',error=repr(e));(S/'verification.json').write_text(json.dumps(out,indent=2)+'\n');raise
(S/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['git_final']},indent=2))
