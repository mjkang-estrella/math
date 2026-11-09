import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r703';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_bytes())
def binding(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 a=binding(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
def dump(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
refs=[I/n for n in ['manifest.json','queue-r704.json','reserved-ids-r704.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','bindings.json','active-breadth-reservations.json']]+[C/'manifest.json',B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
dump('initial-bindings.json',[binding(p) for p in refs])
m=j(I/'manifest.json');names={e['path'] for e in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:check(I/e['path'],e)
pairs=j(I/'bindings.json')
for e in pairs:
 for k in ['original','copy']:check(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');assert (I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()==(C/'manifest.json').read_bytes()
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
flat=refs+[I/e['path'] for e in m['files']]+[pathlib.Path(e[k]) for e in pairs for k in ['original','copy']]+[C/e['path'] for e in chunks+cm['frozen_inputs']]
dump('flat-bindings.json',[binding(p) for p in dict.fromkeys(flat)])
# Only now parse administrative contents and extract assigned scientific records.
cov=j(I/'coverage-delta.json');assert len(cov)==8483
active=j(I/'active-breadth-reservations.json');seen=set()
for a in active:
 s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
ids=set(j(I/'reserved-ids-r704.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r704.json')} and len(ids)==50 and len(seen)==150
found=[]
for e in chunks:
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':e['path'],'corpus_line':n,'record':r,'exact_utf8_statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(found)==50 and {r['mathdb_id'] for r in found}==ids
dump('literal-records.json',found)
dump('pre-reading-checks.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_payload_exact':True,'direct_original_copy_pairs':len(pairs),'chunks_in_place':20,'separately_listed_frozen_inputs':8,'coverage_baseline':8483,'reserved_sets':3,'reserved_total':150,'disjoint':True,'upstream_verifier_executed':False})
print('PASS intake exact payload, direct pairs, 20 chunks, 8 inputs, 150 reserved disjoint; 50 assigned extracted')
