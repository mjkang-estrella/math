import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; L=D.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r603'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def info(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
rows={}
def bind(p,e=None):
 x=info(p)
 if e: assert x['sha256']==e['sha256'] and x['size']==e.get('size',e.get('bytes')),str(p)
 rows[str(p)]=x
 return x
for p in I.iterdir():
 if p.is_file():bind(p)
m=load(I/'manifest.json'); assert set(x['path'] for x in m['files'])=={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e)
for e in load(I/'bindings.json'):
 bind(pathlib.Path(e['original']),e);bind(pathlib.Path(e['copy']),e)
rm=load(R/'manifest.json'); chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:bind(R/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
a=load(I/'reserved-ids.json');q=load(I/'queue.json');c=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
assert len(c)==6033 and len(q)==50 and [x['mathdb_id'] for x in q]==a['ids'] and len(set(a['ids']))==50
seen=set(); cov=set(map(int,c)); protected=set(a['protected_ids']); lanes=[]
for x in active:
 s=set(x['ids']);assert len(s)==50 and not s&(seen|cov|protected);seen|=s;lanes.append(x['lane'])
assert set(lanes)=={'claude-mathdb-primary-qualified-breadth-r602','sol-mathdb-primary-qualified-breadth-r604','sol-mathdb-primary-qualified-breadth-r600'},lanes
assert set(a['ids'])<=seen and set(a['other_active_reservations'])==seen-set(a['ids'])
assert len((I/'routing-queue.jsonl').read_text().splitlines())==8000
out=[]
for e in chunks:
 p=R/e['path']
 with p.open() as f:
  for n,line in enumerate(f,1):
   r=json.loads(line)
   if r.get('id',r.get('mathdb_id')) in a['ids']:
    out.append({'corpus_path':str(p),'line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
out.sort(key=lambda x:a['ids'].index(x['record'].get('id',x['record'].get('mathdb_id'))))
(D/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
(D/'binding-verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'paths':len(rows),'chunks_in_place':20,'frozen_inputs':8,'coverage':6033,'routing_metadata_rows':8000,'assignments':lanes,'literal_records':50,'pass':True},indent=2)+'\n')
print('PASS',len(rows),len(out));print(json.dumps(out[0],ensure_ascii=False,indent=2))
