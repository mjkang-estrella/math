import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r537';C=L/'pi-mathdb-full-corpus-inventory-r301';B=L.parent
j=lambda p:json.loads(p.read_text())
h=lambda b:hashlib.sha256(b).hexdigest()
refs={}
def bind(p,e=None):
 b=p.read_bytes();r={'path':str(p),'size':len(b),'sha256':h(b)}
 if e:assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],str(p)
 refs[str(p)]=r
 return r
bind(I/'manifest.json',{'size':12419,'sha256':'a9c103bf1de2a494d49b2669e2076ec456fdd3e8cf4c9bf78eaeb229f7fe24e6'})
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for n in ['ledger.json','prior-campaign-context.json']:bind(B/n)
for n in ['accepted-exclusions.json','historical-dispositions.json']:bind(L/'root-mathdb-accepted-exclusions-r304'/n)
for p in L.glob('*r363*'):
 for f in p.iterdir():
  if f.is_file():bind(f)
bind(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
print('bound',len(refs),'20 chunks; 8 frozen inputs')
q=j(I/'queue.json');ids={r['mathdb_id'] for r in q};assert len(ids)==len(q)==50 and ids==set(j(I/'reserved-ids.json')['ids'])
cov=j(I/'coverage-delta.json');assert len(cov)==4383
seen=set()
for a in j(I/'active-breadth-reservations.json'):
 s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
assert len(seen)==150
found=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'line':n,'record':r,'statement':r['statement'],'statement_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())})
assert len(found)==50
found.sort(key=lambda d:next(i for i,r in enumerate(q) if r['mathdb_id']==d['mathdb_id']))
(P/'assigned-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
(P/'statement-readout.txt').write_text('\n\n'.join(str(i+1)+' ID '+str(d['mathdb_id'])+' '+d['record'].get('title','')+'\n'+d['statement']+'\nSOURCE '+json.dumps(d['record'].get('sources',d['record'].get('references',{})),ensure_ascii=False) for i,d in enumerate(found)))
print('extracted exactly50')
