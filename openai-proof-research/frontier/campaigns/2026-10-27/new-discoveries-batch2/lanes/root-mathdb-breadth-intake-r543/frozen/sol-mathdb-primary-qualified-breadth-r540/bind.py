import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r539';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
bound={}
def bind(p,expected=None):
 p=p.resolve();b=p.read_bytes();e={'path':str(p),'size':len(b),'sha256':h(b)}
 if expected:assert e['size']==expected.get('size',expected.get('bytes')) and e['sha256']==expected['sha256'],str(p)
 bound[str(p)]=e
 return e
for n in ['manifest.json','bindings.json','queue.json','reserved-ids.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json']:bind(I/n)
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:bind(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
# Bind context before reading scientific/admin contents.
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():bind(p)
for p in L.glob('*r363/*'):
 if p.is_file():bind(p)
# Existing flat references remain flat: verify and retain without copying.
for e in j(I/'frozen/sol-mathdb-primary-qualified-breadth-r536/flat-bindings.json'):bind(pathlib.Path(e['path']),e)
(P/'flat-bindings.json').write_text(json.dumps(list(bound.values()),indent=2)+'\n')
res=j(I/'reserved-ids.json');q=j(I/'queue.json');cov=j(I/'coverage-delta.json');assert len(cov)==4433
assert len(q)==len(res['ids'])==50 and {r['mathdb_id'] for r in q}==set(res['ids'])
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
records=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in res['ids']:
   records.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line_1based':n,'statement':r['statement'],'statement_utf8_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'record':r})
assert len(records)==50
records.sort(key=lambda r:res['ids'].index(r['mathdb_id']))
(P/'assigned-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(P/'reading.txt').write_text('\n\n'.join(str(r['mathdb_id'])+'\n'+r['statement']+'\nSOURCE '+json.dumps(r['record'].get('sources',r['record'].get('source')),ensure_ascii=False) for r in records))
print('BIND PASS',len(bound),'files; 20 chunks; 8 frozen inputs; 50 records; reservations disjoint')
print('record keys',records[0]['record'].keys())
print('context bound',*[p for p in bound if 'r304/' in p or 'r363/' in p],sep='\n')
