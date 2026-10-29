from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;V=P.parent/'sol-frank-attenuation-preliminary-review-r1';S=P.parent/'sol-fresh-source-discovery-r136'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((V/'manifest.json').read_text())['files']
for r in rows:assert sha(V/r['path'])==r['sha256'],r['path']
frozen=json.loads((P.parent/'root-frank-attenuation-preliminary-freeze-r1/review-freeze.json').read_text())['files']
for r in frozen:assert sha(S/r['path'])==r['sha256'],r['path']
Q=P/'replay';(Q/'inputs').mkdir(parents=True,exist_ok=True)
shutil.copyfile(V/'independent_check.py',Q/'independent_check.py');shutil.copyfile(S/'certificate.json',Q/'inputs/certificate.json')
(P/'integrity.json').write_text(json.dumps({'status':'PASS','review_manifest':len(rows),'candidate_freeze':len(frozen)},indent=2)+'\n')
print('review',len(rows),'candidate',len(frozen))
