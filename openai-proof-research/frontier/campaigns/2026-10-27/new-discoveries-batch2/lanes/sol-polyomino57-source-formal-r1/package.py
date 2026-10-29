from pathlib import Path
import json,hashlib,zipfile,shutil
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for e in json.loads((L/'hash-before.json').read_text()):
 p=Path(e['path']);q=Path(e['copy'])
 assert sha(p)==sha(q)==e['sha256']
 checks.append(dict(path=str(p),copy=str(q),sha256=e['sha256'],unchanged=True))
(L/'hash-after.json').write_text(json.dumps(checks,indent=2)+'\n')
B=L.parent.parent
review=B/'lanes/sol-polyomino57-preliminary-review-r1/review.md'
assert sha(review)==json.loads((L/'INVESTMENT.json').read_text())['review_sha256']
prov=dict(status='FORMAL_COMPONENTS_ONLY',fullSourceClaim=False,credit=0,counts=dict(additional=5,total=35),root_decision='INVEST_NOT_ACCEPTED',independent_review=dict(path=str(review),sha256=sha(review)),original_candidate_freeze_sha256=sha(L/'freeze.json'),pins_sha256=sha(L/'pins.json'),source_only_replay_receipt_sha256=sha(L/'verification/receipt.json'),files_unchanged=len(checks),external_actions=False,children=False,git_commands=False,remaining_gaps=json.loads((L/'verification/receipt.json').read_text())['missing'],novelty='No new clearance; inherited bounded prior-art and substantive borderline limitations preserved.',origin_audit=dict(declarations=233,modules=6,unsafe=False,axiom=False,partial_generated=['Polyomino57.attachCheck._unsafe_rec'],allowed_dependencies=['propext','Classical.choice','Quot.sound']))
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
files=['SUMMARY.md','provenance.json','pins.json','run.py','verify.py']+[str(p.relative_to(L)) for p in sorted((L/'formal').glob('*.lean'))]
manifest={p:sha(L/p) for p in files}
(L/'component-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(L/'source-only-components.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for p in files+['component-manifest.json']:
  info=zipfile.ZipInfo(p,date_time=(2026,10,29,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(info,(L/p).read_bytes())
E=L/'extracted-components'
if E.exists():shutil.rmtree(E)
E.mkdir()
with zipfile.ZipFile(L/'source-only-components.zip') as z:z.extractall(E)
for p,h in manifest.items():assert sha(E/p)==h
print('source-only archive',sha(L/'source-only-components.zip'))
