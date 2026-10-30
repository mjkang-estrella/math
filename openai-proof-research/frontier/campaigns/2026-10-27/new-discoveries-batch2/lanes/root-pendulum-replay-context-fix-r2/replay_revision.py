from pathlib import Path
import hashlib,json,subprocess,sys,datetime
P=Path(__file__).resolve().parent;D=P/'packet'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
with (P/'replay.log').open('w') as log:
 subprocess.run([sys.executable,str(D/'replay_guard.py'),sys.executable,str(D/'replay.py'),str(P/'revised-source.zip'),str(P/'fresh-extraction')],stdout=log,stderr=subprocess.STDOUT,check=True)
with (P/'rebuild.log').open('w') as log:
 subprocess.run([sys.executable,str(P/'fresh-extraction/package.py'),str(P/'reproduced.zip')],cwd=P/'fresh-extraction',stdout=log,stderr=subprocess.STDOUT,check=True)
assert sha(P/'revised-source.zip')==sha(P/'reproduced.zip')
r=json.loads((P/'fresh-extraction/replay-receipt.json').read_text());assert r['status']=='MANDATORY_MERGED_SOURCE_ONLY_REPLAY_PASS' and r['declaration_count']==139
for row in json.loads((P/'review-freeze.json').read_text())['files']:
 p=Path(row['path']);assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],str(p)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',mandatory_revised_replay=r['status'],actual_declarations=139,mathematical_modules=14,archive_sha256=sha(P/'revised-source.zip'),byte_identical_rebuild=True,all_originals_unchanged=True,qualification='Only mutable-context replay coupling repaired. Historical coverage and authored PDF/visual QA remain HOLD. Credit zero.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
