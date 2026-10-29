import json,hashlib,itertools
from pathlib import Path
from datetime import datetime,timezone
root=Path(__file__).resolve().parent; lanes=root.parent
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
    return h.hexdigest()
freeze=json.loads((lanes/'root-supertoken-review-freeze-r1/review-freeze.json').read_text())
for row in freeze['files']:
    p=Path(freeze['candidate'])/row['path']
    assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
review=lanes/'sol-supertoken-preliminary-review-r1'
sealed=[]
for p in sorted(review.rglob('*')):
    if p.is_file() and '__pycache__' not in p.parts:
        sealed.append({'path':str(p.relative_to(review)),'sha256':sha(p),'bytes':p.stat().st_size})
(root/'review-freeze.json').write_text(json.dumps({'root':str(review),'files':sealed},indent=2)+'\n')
cases=[]
for m in range(5,21):
    supports=[s for k in range(3) for s in itertools.combinations(range(m),k)]
    codes={tuple(int(i in s)+int(i+1 in s) for i in range(m-1)) for s in supports}
    assert len(codes)==len(supports)
    cases.append({'m':m,'supports':len(supports)})
result={'utc':datetime.now(timezone.utc).isoformat(),'decision':'EXCLUDE: routine classical construction adaptation',
 'source':'PASS','ordinary_math':'PASS','historical_novelty':'HOLD, no exact prior claim identified',
 'candidate_hashes_verified':len(freeze['files']),'review_files_sealed':len(sealed),
 'general_block_checks':cases,'credit':0,'counts':[8,38],
 'stop_investment':['Lean','manuscript','acceptance'],
 'registry_correction':'Old cap is now structurally closed by Renyi r3; target-specific semantic gaps remain. This exclusion does not depend on novelty absence.'}
(root/'EXCLUSION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='general_block_checks'}))
