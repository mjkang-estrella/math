import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r551';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sig(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
refs={}
def bind(p,e=None):
 s=sig(p)
 if e:assert s['sha256']==e['sha256'] and s['size']==e.get('size',e.get('bytes')),str(p)
 refs[str(p)]=s
 return s
for p in sorted(I.iterdir()):
 if p.is_file():bind(p)
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');bind(C/'manifest.json',sig(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():bind(p)
for p in (L/'root-mathdb-breadth-intake-r363').glob('*'):
 if p.is_file():bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(refs),'chunks':20,'frozen_inputs':8,'intake_exact':True,'pairs_checked':len(j(I/'bindings.json'))},indent=2)+'\n')
r=j(I/'reserved-ids.json');q=j(I/'queue.json');assert len(q)==50 and {x['mathdb_id'] for x in q}==set(r['ids'])
cov=j(I/'coverage-delta.json');assert len(cov)==4733
active=j(I/'active-breadth-reservations.json');seen=set()
for a in active:
 ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
out=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  rec=json.loads(line)
  if rec['mathdb_id'] in r['ids']:
   out.append({'mathdb_id':rec['mathdb_id'],'chunk':str(p),'line':n,'record':rec,'statement':rec['statement'],'statement_sha256':hashlib.sha256(rec['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
out.sort(key=lambda x:r['ids'].index(x['mathdb_id']))
(P/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
(P/'reading.txt').write_text('\n\n'.join(str(x['mathdb_id'])+' '+str(x['record'].get('title'))+'\n'+x['statement']+'\nSOURCES '+json.dumps({k:v for k,v in x['record'].items() if k not in ['statement','title']},ensure_ascii=False) for x in out))
print('Bound',len(refs),'files; 20 chunks and 8 inputs; assignments disjoint; extracted 50 statements')
