# Independent read-only validation; no producer/upstream code imported or executed.
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r487';C=L/'pi-mathdb-full-corpus-inventory-r301'
def need(v,m):
 if not v:raise ValueError(m)
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while True:
   b=f.read(1048576)
   if not b:break
   h.update(b);n+=len(b)
 return n,h.hexdigest()
def check(p,x):
 need(digest(p)==(x.get('size',x.get('bytes')),x['sha256']),'bytes mismatch '+str(p))
def exact_manifest(root,excluded):
 m=json.loads((root/'manifest.json').read_text());entries=m['files'];want={x['path'] for x in entries}
 need(len(want)==len(entries),'duplicate manifest entries')
 got={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-excluded
 need(got==want,'exact manifest set mismatch '+str(root))
 for x in entries:check(root/x['path'],x)
 return len(entries)
try:
 payload_count=exact_manifest(P,{'manifest.json','verification-receipt.json'})
 intake_count=exact_manifest(I,{'manifest.json','verification-receipt.json'})
 for x in json.loads((I/'bindings.json').read_text()):
  check(pathlib.Path(x['original']),x);check(pathlib.Path(x['copy']),x)
 flat=json.loads((P/'flat-bindings.json').read_text())
 for x in flat:check(pathlib.Path(x['path']),x)
 inv=json.loads((C/'manifest.json').read_text());chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];frozen=inv['frozen_inputs']
 need(len(chunks)==20 and len(frozen)==8,'inventory cardinality')
 for x in chunks+frozen:check(C/x['path'],x)
 reserve=json.loads((I/'reserved-ids.json').read_text());ids=reserve['ids'];queue=json.loads((I/'queue.json').read_text())
 need(len(ids)==len(set(ids))==50,'own cardinality');need({x['mathdb_id'] for x in queue}==set(ids) and len(queue)==50,'queue mismatch')
 claude=json.loads((L/'root-mathdb-breadth-intake-r479/reserved-ids.json').read_text())['ids'];sol=json.loads((L/'root-mathdb-breadth-intake-r485/reserved-ids.json').read_text())['ids']
 need(len(claude)==len(set(claude))==len(sol)==len(set(sol))==50,'other cardinalities')
 need(not set(claude)&set(sol) and not set(ids)&(set(claude)|set(sol)),'reservation collision')
 need(set(reserve['other_active_reservations'])==set(claude)|set(sol) and len(reserve['other_active_reservations'])==100,'other reservation union')
 need(not set(ids)&{372627,372628,368940,404067,364119},'excluded ID')
 original={}
 for x in chunks:
  p=C/x['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r.get('mathdb_id') in ids:
    need(r['mathdb_id'] not in original,'duplicate original');original[r['mathdb_id']]=(str(p),n,r)
 need(set(original)==set(ids),'original record cardinality')
 ds=json.loads((P/'dispositions.json').read_text());need(len(ds)==50 and {d['mathdb_id'] for d in ds}==set(ids),'disposition set')
 if '--negative-test' in sys.argv:ds[0]['original_literal_statement']+=' MUTATION'
 for d in ds:
  path,n,r=original[d['mathdb_id']]
  need(d['original_chunk']==path and d['original_line']==n,'original locator mismatch')
  need(d['original_literal_statement']==r['statement'],'literal statement mismatch')
  need(hashlib.sha256(r['statement'].encode('utf-8')).hexdigest()==d['statement_utf8_sha256'],'literal digest mismatch')
  need(hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')).hexdigest()==d['canonical_record_sha256'],'canonical digest mismatch')
  need(d['accepted_credit']==0 and d['evidence_levels']['current_registry_cleared'] is False,'credit/registry mismatch')
 coverage=json.loads((P/'coverage-provenance.json').read_text());need(coverage['baseline_reported_literal_reviews']==3433 and coverage['local_new_literal_statement_reviews']==50,'coverage counts')
 need(coverage['counts']=={'additional':9,'total':39,'next':40},'shared count specification')
 need(coverage['other_reservations']=={'claude_r480':claude,'sol_r486':sol},'coverage reservations')
 need(json.loads((P/'proposals.json').read_text())['qualified_briefs']==[],'unexpected proposal')
 print(json.dumps({'status':'PASS','payloads':payload_count,'intake_payloads':intake_count,'flat_actual_references':len(flat),'corpus_chunks':20,'frozen_inputs':8,'own_ids':50,'other_reservations':[50,50],'original_literal_and_canonical_hashes':50,'mathematical_or_novelty_pass':False}))
except Exception as e:
 print(json.dumps({'status':'FAIL','reason':str(e)}));sys.exit(1)
