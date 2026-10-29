import json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(262144),b''):h.update(b)
 return h.hexdigest()
before=json.loads((L/'frozen-before.json').read_text());after=[]
for x in before:
 actual=sha(Path(x['path']));after.append(dict(x,after_sha256=actual,unchanged=actual==x['sha256']))
(L/'frozen-after.json').write_text(json.dumps(after,indent=2))
drift=[x for x in after if not x['unchanged']]
assert drift,'Use original strict finalize.py when no drift exists; this script only seals failed handbacks'
sourcebefore=json.loads((L/'sourcehashes-before.json').read_text());sourceafter={p:sha(L/p) for p in sourcebefore}
(L/'sourcehashes-after.json').write_text(json.dumps(sourceafter,indent=2))
assert sourcebefore==sourceafter,'Local source mutation: cannot even seal source-integrity handback'
assert json.loads((L/'check-results.json').read_text())['status']=='PASS'
receipt={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'status':'NO_ELIGIBLE_FRESH_RESOLUTION; INTEGRITY_HOLD','strict_finalizer':'FAILED; unchanged finalize.py assertion retained','all_frozen_unchanged':False,'drift':drift,'all_local_sources_unchanged':True,'source_hash_entries':len(sourceafter),'audit':json.loads((L/'target-audit-receipt.json').read_text()),'checks':'PASS224exactpaddingcomparisons','note':'Shared NEXT changed during run; no shared edit was issued by this lane. No restoration or hash baseline rewrite. This is not a clean freeze PASS.'}
(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2))
prov=dict(receipt,lane=str(L),sources='http.jsonl; sourcehashes-before.json; sourcehashes-after.json',current_registry='Omega5e2dd09b878d498b14033cbbb1b54be10c590d31; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',novelty='HOLD; current delta capped300files; four screens ineligible independently',helper_guard={'path':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'sha256':sha(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_groupRSS_MiB':512,'CPU_s':210,'wall_s':230,'nominal_ms':40,'BLAS':1},formal_work='none',external_actions='public read-only HTTP/search only; no accounts/browser/posts/uploads',acceptance='none; no shared counts edited')
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
with (L/'finalmanifest.jsonl').open('w') as out:
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in {'finalmanifest.jsonl','seal.log'}:out.write(json.dumps({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in {'audit','drift'}}))
