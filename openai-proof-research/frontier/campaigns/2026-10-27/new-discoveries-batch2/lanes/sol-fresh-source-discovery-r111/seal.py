import json,hashlib,datetime,os
from pathlib import Path
lane=Path(__file__).parent
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
sources=[]
for name in ['source-receipts.jsonl','closest-arxiv.log']:
 with (lane/name).open() as f:
  for line in f:
   if line.strip():sources.append(json.loads(line))
guard=lane.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(lane),'sources':sources,'guard':{'path':str(guard),'sha256':digest(guard)[0],'unchanged':True,'AS_groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1},'upstream':{'repo':'https://github.com/openai/math','pinned':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'},'registry':{'inherited_latest_lawful_omega':'89cda9c274d1122b7676173296af3047c3b64cd1','receipt_utc':'2026-10-29T20:10:57Z','openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','current_prior':'HOLD','access_limits':['known recursive-tree403 and HEAD403 not retried','subsequent 300-file cap unresolved','no reset inferred','path searches not semantic absence evidence']},'status':{'ordinary_math':'complete candidate, self-adversarial check only','independent_review':'not performed (solo instruction)','eligibility':'HOLD unnumbered attributed assertion/classical subsumption','novelty':'HOLD current semantic coverage','Lean':False,'paper':False,'credit':0},'failures':['broad optional inventory signal9 at210.8s; partial bytes retained','CMU closest source404; distinct public arXiv retrieval succeeded','Maxwell/BNT provisional freshness invalidated by expanded screen','numeric scan tiny margins not used as proof','one native grep displayed oversized nested inventory record; no inference from that truncated output'],'scope':'full existential p0 threshold refuted; numbered Shannon claim not resolved','screens':{'required':'screen-receipt.json','semantic':'semantic-screen.log','inventory_content':'required-content.jsonl.gz','inventory_hashes':'required-hashes.jsonl','scope_limit':'text extensions selected by screen.py, binary/PDF inventory excluded; no exhaustive semantic audit of 127827 files'}}
(lane/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
excluded={'manifest.jsonl','manifest-verification.json','seal.log','seal.guard.json'}
with (lane/'manifest.jsonl').open('w') as out:
 for base,ds,fs in os.walk(lane):
  for name in sorted(fs):
   if name in excluded:continue
   p=Path(base,name);h,n=digest(p);row={'path':str(p.relative_to(lane)),'bytes':n,'sha256':h};out.write(json.dumps(row)+'\n');print(json.dumps(row),flush=True)
count=0
with (lane/'manifest.jsonl').open() as f:
 for line in f:
  row=json.loads(line);h,n=digest(lane/row['path']);assert (h,n)==(row['sha256'],row['bytes']);count+=1
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','entries':count,'manifest_sha256':digest(lane/'manifest.jsonl')[0],'method':'streamed64KiB hash generation and independent reread of every payload; JSONL emitted one entry at a time','exclusions':sorted(excluded)}
(lane/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
