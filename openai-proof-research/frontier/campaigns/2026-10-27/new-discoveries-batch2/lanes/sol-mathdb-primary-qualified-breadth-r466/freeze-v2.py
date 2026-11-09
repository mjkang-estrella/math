import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent; P=B.parent.parent.parent.parent
bindings={}
def bind(p):
 p=pathlib.Path(p).resolve(); b=p.read_bytes(); r={'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}; bindings[str(p)]=r; return b
def load(p):return json.loads(bind(p))
def valid(p,e):
 b=bind(p); assert len(b)==e.get('size',e.get('bytes')),str(p); assert hashlib.sha256(b).hexdigest()==e['sha256'],str(p)
for n in ['root-mathdb-breadth-intake-r465','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L.parent/n; m=load(d/'manifest.json'); entries=m if isinstance(m,list) else m.get('files',m.get('entries',[])); assert entries
 for e in entries: valid(d/e['path'],e)
 bp=d/'bindings.json'
 if bp.exists():
  bb=load(bp)
  if isinstance(bb,list):
   for e in bb:
    if 'original' in e: valid(e['original'],e)
inv=L.parent/'pi-mathdb-full-corpus-inventory-r301'; m=load(inv/'manifest.json'); chunks=[e for e in m['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20
for e in chunks:valid(inv/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',P/'sources/upstream.json',P/'sources/CONTENTS.md',P/'sources/preprints-tree.json']:
 if p.exists():bind(p)
# Flat inventory, no recursive reference expansion.
(L/'bindings.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flat_refs':list(bindings.values()),'frozen_inputs':[str(inv/e['path']) for e in chunks]},indent=2)+'\n')
print('PASS direct intake manifests, actual original bindings, exclusions manifests, twenty chunks',len(bindings))
r=load(L.parent/'root-mathdb-breadth-intake-r465/reserved-ids.json'); ids=set(r['ids']); assert len(ids)==50
records=[]
for e in chunks:
 for line,s in enumerate((inv/e['path']).open(),1):
  x=json.loads(s)
  if x.get('id',x.get('mathdb_id')) in ids:records.append({'chunk':e['path'],'line':line,'record':x})
assert len(records)==50, len(records)
(L/'assigned-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('Extracted 50 originals after hash verification; keys',records[0]['record'].keys())
