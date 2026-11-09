from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,datetime
from ap_classifier import check
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert all(x['file'] not in ['manifest.json','verification-receipt.json'] for x in manifest)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual=={x['file'] for x in manifest}
for r in manifest:assert sha(L/r['file'])==r['sha256'],r['file']
for idx in ['bindings.json','history-bindings.json']:
 for r in json.loads((L/idx).read_text()):
  assert sha(Path(r['original']))==r['sha256'],r['original']
  assert sha(L/r['copy'])==r['sha256'],r['copy']
for r in json.loads((L/'derived-bindings.json').read_text()):assert sha(L/r['file'])==r['sha256']
for r in json.loads((L/'access.json').read_text()):
 if 'sha256' in r:assert sha(L/r['file'])==r['sha256']
for row in json.loads((L/'classification-checks.json').read_text()):assert check(row['a'],row['t'])==row['result']
d=json.loads((L/'frozen/030-lines-result-12.json').read_text())
ap=next(x for x in d['supports'] if x['support']==[1,-2,1])
assert all(Q(s['parameter'][1])<=Q(10,9) for s in ap['segments'])
for v in ap['vertices']:
 x=Q(v['point'][0]);a=x.denominator;t=x.numerator-a
 if x>Q(10,9):assert a<12 or (a,t)==(13,2)
for r in manifest:assert sha(L/r['file'])==r['sha256'],r['file']
receipt=dict(status='PASS',time=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'manifest.json'),files=len(manifest),original_and_copy_bindings='PASS',regression_witness_replay='PASS',ratio_extraction='PASS; frozen upstream computation, no full geometry rerun',scope='custody and executable checks only; not independent mathematical acceptance',counts=dict(additional=9,total=39,next=40))
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
