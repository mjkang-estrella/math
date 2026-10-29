import json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(262144),b''):h.update(b)
 return h.hexdigest()
assert (L/'target-audit-receipt.json').exists(),'Audit must finish and preserve its receipt before sealing'
before=json.loads((L/'frozen-before.json').read_text());after=[]
for x in before:
 p=Path(x['path']);actual=digest(p)
 after.append(dict(x,after_sha256=actual,unchanged=actual==x['sha256']))
(L/'frozen-after.json').write_text(json.dumps(after,indent=2))
sourcebefore=json.loads((L/'sourcehashes-before.json').read_text());sourceafter={p:digest(L/p) for p in sourcebefore}
(L/'sourcehashes-after.json').write_text(json.dumps(sourceafter,indent=2))
assert all(x['unchanged'] for x in after),'Frozen-source drift: receipt preserved'
assert sourceafter==sourcebefore,'Local source drift: receipt preserved'
check=json.loads((L/'check-results.json').read_text());assert check['status']=='PASS'
audit=json.loads((L/'target-audit-receipt.json').read_text())
prov={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'lane':str(L),'status':'NO_ELIGIBLE_FRESH_RESOLUTION','source_receipts':'http.jsonl','source_hashes_before':'sourcehashes-before.json','source_hashes_after':'sourcehashes-after.json','frozen_before':'frozen-before.json','frozen_after':'frozen-after.json','sources_unchanged':True,'original_audit':audit,'early_audit':'audit-receipts.jsonl','current_registry':'Omega5e2dd09b878d498b14033cbbb1b54be10c590d31; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','novelty_clearance':'HOLD: capped300-file current delta; binary originals/unexamined bodies; no positive nominee','excluded_echoes':'target-exclusions.jsonl; r111/r112/r113 JSONL explicitly excluded','checks':{'status':check['status'],'exact_padding_checks':check['exact_padding_checks']},'helper_guard':{'path':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'sha256':digest(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_and_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_sampling_ms':40,'BLAS_threads':1},'formal_work':'none; no Lean or paper authorized/attempted','external_actions':'public read-only HTTP/search only; no accounts/browser/posts/uploads','limits':'No worldwide novelty absence claim, no acceptance, no shared counters touched.'}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
receipt={'utc':prov['utc'],'frozen_hash_entries':len(after),'all_frozen_unchanged':True,'source_hash_entries':len(sourceafter),'all_local_sources_unchanged':True,'audit_complete':audit['complete'],'checks':'PASS','status':prov['status']}
(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2))
with (L/'finalmanifest.jsonl').open('w') as out:
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in {'finalmanifest.jsonl','seal.log'}:
   out.write(json.dumps({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':digest(p)})+'\n')
print(json.dumps(receipt))
