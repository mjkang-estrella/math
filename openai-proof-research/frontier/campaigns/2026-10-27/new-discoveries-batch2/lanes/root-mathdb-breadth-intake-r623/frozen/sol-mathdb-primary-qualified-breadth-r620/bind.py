from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r619';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
bindings={}
def bind(p,e=None):
 p=p.resolve();b=p.read_bytes();d={'path':str(p),'sha256':h(b),'size':len(b)}
 if e:assert d['sha256']==e['sha256'] and d['size']==e.get('size',e.get('bytes')),str(p)
 bindings[str(p)]=d
 return d
bind(I/'manifest.json',{'sha256':'a822fe2bd22562b647b3521fcc2d999495d5359e5c56eedfbc16e0cbdf65b961','size':10108})
m=j(I/'manifest.json')
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(Path(e[k]),e)
cm=j(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for n in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','root-mathdb-cayley-review-intake-r363/manifest.json']:
 bind(L/n)
for n in ['ledger.json','prior-campaign-context.json']:bind(L.parent/n)
for n in ['upstream.json','CONTENTS.md','preprints-tree.json']:bind(L.parents[4]/'sources'/n)
(P/'flat-bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
cov=j(I/'coverage-delta.json');active=j(I/'active-breadth-reservations.json');q=j(I/'queue-r620.json');res=j(I/'reserved-ids-r620.json');ids=set(res['ids'])
assert len(cov)==6433 and len(active)==2 and len(ids)==len(q)==50 and ids=={r['mathdb_id'] for r in q}
seen=set()
for a in active:
 s=set(a['ids']);assert not s&seen and not s&set(map(int,cov)) and not s&{338366,338408};seen|=s
assert ids<=seen
records=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:records.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'record':r,'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'statement_utf8_sha256':h(r['statement'].encode())})
assert len(records)==50
(P/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'corpus_chunks':20,'frozen_inputs':8,'baseline':6433,'breadth_reservations':2,'assigned_literal_records':50,'flat_bound_files':len(bindings)},indent=2)+'\n')
print('BOUND',len(bindings))
