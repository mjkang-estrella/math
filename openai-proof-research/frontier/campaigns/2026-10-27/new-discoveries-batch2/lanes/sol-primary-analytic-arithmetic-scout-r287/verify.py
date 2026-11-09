from pathlib import Path
import json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mf=json.loads((L/'MANIFEST.json').read_text());bad=[]
for name,r in mf.items():
 if h(L/name)!=r['sha256'] or (L/name).stat().st_size!=r['bytes']:bad.append(name)
bindings=[json.loads(x) for x in (L/'primarybindings.jsonl').read_text().splitlines()];original_drift=[]
for r in bindings:
 if h(Path(r['copy']))!=r['sha256']:bad.append('copy:'+r['copy'])
 if not r['administrative'] and h(Path(r['original']))!=r['sha256']:original_drift.append(r['original'])
reference_count=0
for name in ['cache-references.json','registry-references.json']:
 for r in json.loads((L/name).read_text()):
  reference_count+=1
  if h(Path(r['path']))!=r['sha256']:original_drift.append(r['path'])
# Separate verification: exact rational certificate checked by a process under this same outer guard.
p=subprocess.run([sys.executable,str(L/'witness_verify.py')],capture_output=True,text=True,timeout=60)
assert p.returncode==0,p.stderr
# Checker regenerates the identical existing JSON; prove it did not invalidate manifest.
assert h(L/'witness-verification.json')==mf['witness-verification.json']['sha256']
out=dict(status='PASS' if not bad and not original_drift else 'FAIL',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'MANIFEST.json'),manifest_excludes=['MANIFEST.json','verification-receipt.json'],files_verified=len(mf),frozen_bindings_verified=len(bindings),immutable_references_rechecked=reference_count,manifest_or_copy_failures=bad,scientific_original_drift=sorted(set(original_drift)),witness=json.loads(p.stdout),administrative_originals='snapshot-only, no live identity assertion',scope='no acceptance or novelty clearance')
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out));assert out['status']=='PASS'
