from pathlib import Path
import json,hashlib,datetime,sys
R=Path(__file__).resolve().parent;L=R.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def load(p):return json.loads(p.read_bytes())
def check(p,e):
 need(p.is_file() and not p.is_symlink(),'missing/nonregular '+str(p));b=p.read_bytes();need(H(b)==e['sha256'],'hash '+str(p));need(len(b)==e.get('size',e.get('bytes',len(b))),'size '+str(p))
def manifest(p):
 obj=load(p/'manifest.json');entries=obj['files'] if isinstance(obj,dict) else obj
 for e in entries:check(p/e['path'],e)
 return entries
# exact local inventory: only manifest itself and receipt are excluded.
m=load(R/'manifest.json');actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
need(actual=={e['path'] for e in m['files']},'output inventory mismatch')
for e in m['files']:check(R/e['path'],e)
refs=load(R/'input-bindings.json');need(len(refs)==len({e['path'] for e in refs}),'duplicate input bindings')
for e in refs:check(Path(e['path']),e)
I=L/'root-mathdb-breadth-intake-r379';manifest(I)
for e in load(I/'bindings.json'):check(Path(e['original']),e)
reservation=load(I/'reserved-ids.json');a=reservation['ids'];q=load(I/'queue.json');cov=load(I/'coverage-delta.json')
need(reservation['lane']==R.name,'wrong assigned lane');need(len(a)==len(set(a))==50,'reservation cardinality')
need(len(q)==50 and set(a)=={x['mathdb_id'] for x in q},'queue/reservation exactset')
need(reservation['other_active_reservations']==[],'other active reservation')
need(len(cov)==983 and not set(map(str,a))&set(cov),'baseline coverage overlap')
need(not set(a)&{372627,372628,368940},'reserved review/pending overlap')
C=L/'pi-mathdb-full-corpus-inventory-r301';cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
need(len(chunks)==20,'twenty corpus chunks required');found={}
for e in chunks:
 check(C/e['path'],e)
 for line in (C/e['path']).read_text().splitlines():
  x=json.loads(line);n=int(x.get('mathdb_id',x.get('id',0)))
  if n in a:need(n not in found,'duplicate corpus ID');found[n]=x
records=load(R/'records.json');need(len(records)==50 and {x['mathdb_id'] for x in records}==set(a),'record exactset')
for x in records:need(x==found[x['mathdb_id']],'actual corpus record mismatch')
d=load(R/'dispositions.json');need(len(d)==50 and {x['mathdb_id'] for x in d}==set(a),'disposition exactset')
for x in d:
 original=found[x['mathdb_id']];need(x['statement']==original['statement'] and x['statement_sha256']==H(original['statement'].encode()),'literal text/hash')
 need(x['record_sha256_canonical_json']==H(json.dumps(original,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'record hash')
 need(bool(x['reason']) and x['credit']==0 and not x['proposal'],'disposition integrity')
for n in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:manifest(L/n)
need(load(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['credit']==0,'Cayley exclusion')
for e in load(R/'source-provenance.json'):
 if 'path' in e:check(R/e['path'],e)
need(load(R/'proposals.json')==[],'unexpected proposal')
p=load(R/'provenance.json');need(p['coverage_baseline']==983 and p['counts_unchanged']=={'additional':9,'total':39,'next':40},'count policy')
need(p['primary_body_selected']==18 and sum(x['evidence_level']=='primary_body_selected' for x in d)==18,'primary count')
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':H((R/'manifest.json').read_bytes()),'output_files':len(actual),'original_input_bindings':len(refs),'intake_original_bindings':len(load(I/'bindings.json')),'corpus_chunks_rehashed_in_place':20,'exact_reserved_records_and_dispositions':50,'baseline':983,'disjoint':True,'no_other_active_breadth_reservation':True,'protected_ids':[372627,372628,368940],'scientific_claim':'Artifact and exact-scope integrity only; no independent proof or novelty certification.'}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
