from pathlib import Path
import hashlib,json,zipfile,subprocess,sys,datetime,shutil
R=Path(__file__).resolve().parent
L=R.parent
S=L/'sol-pendulum-manuscript-packet-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def check(rows):
 for r in rows:
  p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
freeze=json.loads((L/'root-pendulum-merged-packet-adoption-r1/review-freeze.json').read_text())['files']
check(freeze)
inputs=[L/'root-pendulum-merged-packet-adoption-r1/review-freeze.json']
for n in ['sol-pendulum-time-map-preliminary-review-r1','sol-pendulum-source-subsumption-review-r2','sol-pendulum-investment-review-r3']:
 inputs.extend(p for p in (L/n).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
inputs.extend([L.parent/n for n in ['AGENTS.md','ledger.json','prior-campaign-context.json','NEXT.md']])
inputs.extend(p for p in L.glob('root-pendulum-*/**/*') if p.is_file() and p.name in ['DECISION.md','REVIEW-ADOPTION.md','decision.md'])
rows=freeze+[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(inputs))]
(R/'before-originals.json').write_text(json.dumps({'utc':stamp(),'files':rows},indent=2)+'\n')
for r in rows:
 p=Path(r['path']);dest=R/'copies'/p.relative_to(L.parent);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);assert sha(dest)==r['sha256']
z=S/'merged-source.zip';assert sha(z)=='cd5c7e4ce387b810dcd5b96f307a23b9ab688db3bb4b4908373496e28eee1fd6'
with zipfile.ZipFile(z) as f:
 names=f.namelist();m=json.loads(f.read('manifest.json'));assert len(names)==len(set(names));assert set(names)==set(m)|{'manifest.json'}
 for n,h in m.items():assert hashlib.sha256(f.read(n)).hexdigest()==h
 assert not any(n.endswith(('.olean','.ilean','.ir','.pyc','.so','.o','.olean.private','.olean.server')) for n in names)
(R/'archive-check.json').write_text(json.dumps(dict(utc=stamp(),sha256=sha(z),payload_files=len(m),manifest=m,duplicates=False,compiled_artifacts=False),indent=2)+'\n')
# replay_guard and guard create separate process groups: the helper ceiling applies
# to this coordinator, while the unchanged Lean guard enforces its own ceiling.
assert (R/'replay.log').exists() # retain mandatory replay failure verbatim
subprocess.run([sys.executable,str(S/'packet/replay_guard.py'),sys.executable,str(R/'strict_modules.py')],check=True)
with (R/'rebuild.log').open('w') as log:
 subprocess.run([sys.executable,str(R/'fresh-extraction/package.py'),str(R/'reproduced.zip')],cwd=R/'fresh-extraction',stdout=log,stderr=subprocess.STDOUT,check=True)
assert sha(R/'reproduced.zip')==sha(z)
check(rows)
for r in rows:assert sha(R/'copies'/Path(r['path']).relative_to(L.parent))==r['sha256']
(R/'after-originals.json').write_text(json.dumps({'utc':stamp(),'files':rows,'originals_and_copies_unchanged':True},indent=2)+'\n')
receipt=json.loads((R/'strict-modules-receipt.json').read_text())
assert receipt['declaration_count']==139 and len(receipt['steps'])==15
(R/'verification-receipt.json').write_text(json.dumps(dict(utc=stamp(),status='STRICT_MODULES_PASS_MANDATORY_REPLAY_HOLD',original_count=len(rows),root_frozen_files=len(freeze),archive_payload_files=len(m),archive_sha256=sha(z),byte_identical_rebuild=True,modules=14,actual_declarations=139,visual_QA='NOT_PERFORMED',resource_qualification='RSS sampled, not continuous peak guarantee'),indent=2)+'\n')
print('INDEPENDENT ARCHIVE, REPLAY, REBUILD, BEFORE/AFTER PASS',flush=True)
