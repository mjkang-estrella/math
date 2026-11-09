import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; refs={}
def bind(p,role):
 p=pathlib.Path(p).resolve(); b=p.read_bytes(); e={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'role':role}; refs[str(p)]=e; return b
def j(p,role):return json.loads(bind(p,role))
def check(p,e,role):
 b=bind(p,role); assert len(b)==e.get('size',e.get('bytes',len(b))),str(p); assert hashlib.sha256(b).hexdigest()==e['sha256'],str(p)
I=B/'root-mathdb-breadth-intake-r471'; V=B/'pi-mathdb-full-corpus-inventory-r301'
for lane in [I,B/'root-mathdb-accepted-exclusions-r304',B/'root-mathdb-cayley-review-intake-r363']:
 for p in lane.iterdir():
  if p.is_file():bind(p,'direct administrative/history input; frozen before scientific read')
 m=j(lane/'manifest.json','manifest')
 for e in (m if isinstance(m,list) else m['files']): check(lane/e['path'],e,'manifest payload direct reference')
# Exactly one level of original bindings; never recurse into bound manifests or binding tables.
for e in j(I/'bindings.json','intake original map'):
 check(e['original'],e,'actual original from intake binding');check(e['copy'],e,'intake frozen counterpart')
m=j(V/'manifest.json','inventory manifest'); chunks=[e for e in m['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
assert len(chunks)==20,len(chunks)
assert len(m['frozen_inputs'])==8
for e in chunks+m['frozen_inputs']:check(V/e['path'],e,'inventory chunk' if e in chunks else 'inventory separately listed frozen input')
for p in ['ledger.json','prior-campaign-context.json']:bind(L.parent.parent/p,'campaign context')
R=L.parents[5]
for p in ['upstream.json','CONTENTS.md','preprints-tree.json']:bind(R/'sources'/p,'repository source context')
(L/'bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','flat_references':len(refs),'chunks':20,'frozen_inputs':8,'upstream_code_executed':False},indent=2)+'\n')
print('PASS',len(refs))
