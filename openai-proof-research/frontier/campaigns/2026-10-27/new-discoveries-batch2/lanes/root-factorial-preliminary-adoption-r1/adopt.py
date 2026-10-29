import json,hashlib
from pathlib import Path
from fractions import Fraction
from datetime import datetime,timezone
root=Path(__file__).resolve().parent; lanes=root.parent
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
    return h.hexdigest()
review=lanes/'sol-factorial-product-preliminary-review-r1'
manifest=json.loads((review/'final-manifest.json').read_text())
for row in manifest['files']:
    p=review/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
freeze=json.loads((lanes/'root-factorial-product-review-freeze-r1/review-freeze.json').read_text())
for row in freeze['files']:
    p=Path(freeze['candidate'])/row['path'];assert sha(p)==row['sha256']
margin=Fraction(2,3)-Fraction(125506,200000)
assert margin>0
data={'utc':datetime.now(timezone.utc).isoformat(),'source':'PASS','math':'PASS',
 'substantive':'scoped provisional PASS; complete counting objection retained',
 'novelty':'HOLD pending targeted current/historical closure','credit':0,'counts':[8,38],
 'review_manifest_entries_verified':len(manifest['files']),'candidate_files_verified':len(freeze['files']),
 'counting_constant_margin_using_log2_gt_two_thirds':str(margin)}
(root/'ADOPTION.json').write_text(json.dumps(data,indent=2)+'\n')
rows=manifest['files']+[{'path':'final-manifest.json','sha256':sha(review/'final-manifest.json'),'bytes':(review/'final-manifest.json').stat().st_size}]
(root/'review-freeze.json').write_text(json.dumps({'root':str(review),'files':rows},indent=2)+'\n')
formal=lanes/'sol-renyi-threshold-source-formal-r1'
fm=json.loads((formal/'manifest.json').read_text())
for path,h in fm.items():assert sha(formal/path)==h,path
receipt=json.loads((formal/'replay-fresh/replay-receipt.json').read_text())
assert receipt['source_claim_pass'] is False and receipt['declaration_count']==51
assert sha(formal/'component-source.zip')==receipt['archive_sha256']
for d in receipt['declarations']:
    assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
    assert not d['unsafe']
for s in receipt['steps']: assert s['exit']==0
rf=lanes/'root-renyi-component-adoption-r1';rf.mkdir(exist_ok=True)
frozen={p:h for p,h in fm.items()}
for name in ['manifest.json','component-source.zip','FINAL-RECEIPT.json','replay-fresh/replay-receipt.json']:
    frozen[name]=sha(formal/name)
(rf/'component-freeze.json').write_text(json.dumps({'root':str(formal),'files':frozen},indent=2)+'\n')
(rf/'ADOPTION.json').write_text(json.dumps({'utc':data['utc'],'status':'PARTIAL COMPONENT ONLY',
 'manifest_verified':len(fm),'declarations_in_worker_replay':51,'source_claim_pass':False,
 'root_verification':'Source interfaces and DCT/log-concavity/profile bodies read; manifest/archive and audit receipts checked. No new root compile claimed.',
 'remaining':['tail-deficit identity','baseline exponential facts','entropy comparison','source negation'],
 'credit':0,'counts':[8,38]},indent=2)+'\n')
print(json.dumps(data));print('Renyi component hashes and 51-declaration worker audit checked; full endpoint open.')
