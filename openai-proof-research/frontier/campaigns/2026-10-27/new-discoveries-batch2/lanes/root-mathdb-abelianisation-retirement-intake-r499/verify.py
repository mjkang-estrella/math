from pathlib import Path
import hashlib,json,sys
from datetime import datetime,timezone
R=Path(__file__).resolve().parent;L=R.parent;F=R/'frozen';C=F/'sol-mathdb-abelianisation-source-prior-review-r496';I=L/'pi-mathdb-full-corpus-inventory-r301';BASE=F/'root-mathdb-three-candidate-intake-r493'
def read(p):return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,r):assert p.is_file() and p.stat().st_size==r.get('size',r.get('bytes')) and sha(p)==r['sha256'],str(p)
def names(p,exc):return {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}-set(exc)
def put(n,x):(R/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
bindings=read(R/'bindings.json')
for r in bindings:check(Path(r['original']),r);check(Path(r['copy']),r)
cm=read(C/'manifest.json');exc={'manifest.json','final-receipt.json'}
assert set(cm['excluded_exact_paths'])==exc and len(cm['files'])==21
assert names(C,exc)=={r['path'] for r in cm['files']}==names(L/C.name,exc)
for r in cm['files']:check(C/r['path'],r)
refs=read(C/'input-bindings.json')
for r in refs:check(Path(r['path']),r)
flat=read(C/'flat-original-bindings.json')
for row in flat:
 for kind in ['original','intake_copy','retained']:check(Path(row[kind]['path']),row[kind])
receipt=read(C/'final-receipt.json');assert receipt['status']=='PASS' and receipt['manifest_sha256']==sha(C/'manifest.json') and receipt['counts']=={'additional':9,'total':39,'next':40}
coverage=read(BASE/'coverage-delta.json');assert len(coverage)==3683
assert read(BASE/'active-breadth-reservations.json')==[]
im=read(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');assert im==read(I/'manifest.json')
chunks=[r for r in im['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(im['frozen_inputs'])==8
for r in chunks+im['frozen_inputs']:check(I/r['path'],r)
adjudications=read(BASE/'adjudications.json')
adjudications['339564']={'disposition':'RETIRE_PUBLICLY_RESOLVED','credit':0,'review':'sol-mathdb-abelianisation-source-prior-review-r496/review.md','source':'Noferini–Williams, Linear Algebra and its Applications 708 (2025), 372–404, Theorem 4.10 and Corollary 4.12','doi':'10.1016/j.laa.2024.12.003','scope':'Complete target n>=8, gcd(n,6)=2; explicit identification of source Conjecture 4.4','author_proof_audited':False,'current_registry_cleared':False}
hypotheses=read(BASE/'hypothesis-queue.json')
for h in hypotheses:
 if h['mathdb_id']==339564:h['status']='retired_public_resolution'
queue=[json.loads(s) for s in (F/'root-mathdb-breadth-intake-r415/routing-queue.jsonl').read_text().splitlines()]
selected=[];seen=set(coverage)|set(adjudications)|{'372628','368940','404067','364119','338290','337963'}
for r in queue:
 n=str(r['mathdb_id'])
 if n in seen or r['status']!='open' or r['statement_completeness']!='full':continue
 selected.append(r);seen.add(n)
 if len(selected)==50:break
assert len(selected)==50
reservation={'ids':[r['mathdb_id'] for r in selected],'lane':'sol-mathdb-primary-qualified-breadth-r500','status':'reserved_not_reviewed','other_active_reservations':[],'active_hypothesis_ids':[338290,337963]}
outputs={'coverage-delta.json':coverage,'adjudications.json':adjudications,'hypothesis-queue.json':hypotheses,'queue.json':selected,'reserved-ids.json':reservation}
ownexc={'manifest.json','verification-receipt.json'}
if sys.argv[1:]==['build']:
 for n,x in outputs.items():put(n,x)
 put('manifest.json',{'files':[{'path':s,'size':(R/s).stat().st_size,'sha256':sha(R/s)} for s in sorted(names(R,ownexc))],'excluded_exact_paths':sorted(ownexc)})
elif sys.argv[1:]==['verify']:
 for n,x in outputs.items():assert read(R/n)==x
 own=read(R/'manifest.json')['files'];assert names(R,ownexc)=={r['path'] for r in own}
 for r in own:check(R/r['path'],r)
 put('verification-receipt.json',{'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'root_bindings':len(bindings),'review_payloads':21,'input_reference_entries':len(refs),'original_copy_retained_triples':len(flat),'original_corpus_chunks':20,'inventory_frozen_inputs':8,'reported_statement_reviews':3683,'new_breadth_reservations':50,'accepted_counts':[9,39,40],'root_mathematical_replay':False})
else:raise SystemExit('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews; reserved',len(selected))
