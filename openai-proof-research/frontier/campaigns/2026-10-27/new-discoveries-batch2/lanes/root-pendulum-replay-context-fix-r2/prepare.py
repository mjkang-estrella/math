from pathlib import Path
import hashlib,json,zipfile,subprocess,sys,datetime,difflib
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent
S=L/'sol-pendulum-manuscript-packet-r1';V=L/'sol-pendulum-merged-proof-review-r1';D=P/'packet'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
m=json.loads((V/'final-manifest.json').read_text())
for n,r in m['files'].items():check(V/n,r)
assert {str(p.relative_to(V)) for p in V.rglob('*') if p.is_file() and p.name not in m['excludes']}==set(m['files'])
freeze=[]
for source in [S,V]:
 for p in sorted(source.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or any(p.name.endswith(e) for e in ['.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so','.pyc']):continue
  freeze.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
z=S/'merged-source.zip';assert sha(z)=='cd5c7e4ce387b810dcd5b96f307a23b9ab688db3bb4b4908373496e28eee1fd6'
assert not D.exists()
with zipfile.ZipFile(z) as f:
 manifest=json.loads(f.read('manifest.json'));assert set(f.namelist())==set(manifest)|{'manifest.json'}
 for n,h in manifest.items():assert hashlib.sha256(f.read(n)).hexdigest()==h
 f.extractall(D)
records=json.loads((D/'input-records.json').read_text())
contexts={str(B/n) for n in ['AGENTS.md','ledger.json','NEXT.md','prior-campaign-context.json']}
policy=[r for r in records if r['original'] in contexts];assert len(policy)==4
assert not any(r['path'] in contexts for r in json.loads((D/'originals-before.json').read_text()))
(D/'context-snapshot-policy.json').write_text(json.dumps({'purpose':'Historical campaign context is verified against the archived snapshot, never the evolving live context. Scientific inputs and package pins retain original-byte checks.','records':policy},indent=2)+'\n')
old=(D/'verify_inputs.py').read_text()
needle="for row in json.loads((R/'input-records.json').read_text()):\n assert sha(R/row['copy'])==sha(pathlib.Path(row['original']))==row['sha256'],row\nprint(json.dumps({'pins_verified':len(pins['packages']),'frozen_entries_verified':len(json.loads((R/'originals-before.json').read_text())),'originals_and_copies_unchanged':True}))"
replacement="""records=json.loads((R/'input-records.json').read_text())
policy=json.loads((R/'context-snapshot-policy.json').read_text())['records']
assert len(policy)==4 and len({row['original'] for row in policy})==4
assert {pathlib.Path(row['original']).name for row in policy}=={'AGENTS.md','ledger.json','NEXT.md','prior-campaign-context.json'}
assert all(row in records for row in policy)
for row in records:
 assert sha(R/row['copy'])==row['sha256'],row
 if row not in policy:assert sha(pathlib.Path(row['original']))==row['sha256'],row
print(json.dumps({'pins_verified':len(pins['packages']),'frozen_entries_verified':len(json.loads((R/'originals-before.json').read_text())),'scientific_originals_and_copies_unchanged':True,'archived_context_snapshots_verified':len(policy),'live_context_required':False}))"""
assert old.count(needle)==1
new=old.replace(needle,replacement);(D/'verify_inputs.py').write_text(new)
(P/'verifier.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='original/verify_inputs.py',tofile='revised/verify_inputs.py')))
note='\n## Root replay correction, 30 October 2026\n\nThe independent review found that live NEXT.md drift blocked the original archive replay before compilation. This edition keeps all 14 mathematical modules, FullAudit, actual declaration/dependency tables, guards, pins and historical input bytes unchanged. Four administrative context records (AGENTS.md, ledger.json, NEXT.md, prior-campaign-context.json) are now validated solely as archived snapshots. Every scientific original and its copy still undergo the original hash checks. No live context is restored or edited by replay. The original failed replay remains in the independent review lane. Historical coverage, PDF authoring and visual QA holds remain open. No acceptance or count change.\n'
(D/'README.md').write_text((D/'README.md').read_text()+note)
(D/'REPLAY-REVISION.md').write_text(note)
changes=[]
for n,h in manifest.items():
 if sha(D/n)!=h:changes.append(n)
assert set(changes)=={'README.md','verify_inputs.py'}
newmanifest={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(newmanifest,indent=2)+'\n')
with (P/'package.log').open('w') as log:subprocess.run([sys.executable,str(D/'package.py'),str(P/'revised-source.zip')],stdout=log,stderr=subprocess.STDOUT,check=True)
# Rejection controls: archived administrative bytes remain mandatory, as do scientific copies.
controls=[]
for row in [policy[0],next(r for r in records if r not in policy)]:
 p=D/row['copy'];saved=p.read_bytes();p.write_bytes(saved+b'\nTAMPER CONTROL\n')
 try:
  r=subprocess.run([sys.executable,str(D/'verify_inputs.py')],capture_output=True,text=True);assert r.returncode!=0
  controls.append(dict(copy=row['copy'],rejected=True,stderr=r.stderr))
 finally:p.write_bytes(saved)
with (P/'inputs.log').open('w') as log:subprocess.run([sys.executable,str(D/'verify_inputs.py')],stdout=log,stderr=subprocess.STDOUT,check=True)
for n,h in newmanifest.items():assert sha(D/n)==h
for r in freeze:check(Path(r['path']),r)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PREPARED',review_manifest_files=len(m['files']),frozen_files=len(freeze),original_zip_sha256=sha(z),revised_zip_sha256=sha(P/'revised-source.zip'),changed_existing_payloads=changes,added_payloads=['context-snapshot-policy.json','REPLAY-REVISION.md'],mathematical_sources_unchanged=True,administrative_snapshots=policy,negative_controls=controls)
(P/'preparation-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ['negative_controls','administrative_snapshots']}))
