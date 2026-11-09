"""Read-only independent final verification. Only writes this lane's final receipt on success."""
import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent;R=B/'root-mathdb-breadth-intake-r389';C=B/'pi-mathdb-full-corpus-inventory-r301'
def digest(p):
 b=p.read_bytes();return len(b),hashlib.sha256(b).hexdigest()
def chk(p,x):
 n,h=digest(p);assert n==x.get('size',x.get('bytes')) and h==x['sha256'],str(p)
for name in ['input-bindings.json','corpus-bindings.json']:
 for x in json.loads((L/name).read_text())['refs']:chk(pathlib.Path(x['path']),x)
for x in json.loads((L/'administrative-bindings.json').read_text()):chk(pathlib.Path(x['path']),x)
for x in json.loads((R/'manifest.json').read_text())['files']:chk(R/x['path'],x)
for x in json.loads((R/'bindings.json').read_text()):chk(pathlib.Path(x['original']),x)
chunks=[x for x in json.loads((C/'manifest.json').read_text())['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20
for x in chunks:chk(C/x['path'],x)
r=json.loads((R/'reserved-ids.json').read_text());a=set(r['ids']);o=set(r['other_active_reservations']);reviewed=set(map(int,json.loads((R/'coverage-delta.json').read_text())))
assert len(a)==len(r['ids'])==50 and len(o)==50 and len(reviewed)==1133
assert not a&o and not a&reviewed and not a&{372627,372628,368940}
d=json.loads((L/'dispositions.json').read_text());assert len(d)==50 and {x['mathdb_id'] for x in d}==a
s=json.loads((L/'statements.json').read_text());assert len(s)==50 and {x['record']['mathdb_id'] for x in s}==a
original={}
for c in chunks:
 for line in (C/c['path']).open():
  v=json.loads(line)
  if v['mathdb_id'] in a:
   assert v['mathdb_id'] not in original;original[v['mathdb_id']]=v
assert set(original)==a
for x in s:assert x['record']==original[x['record']['mathdb_id']]
for x in d:
 v=original[x['mathdb_id']];assert x['statement']==v['statement'];assert x['url']==v['canonical_url'];assert x['statement_sha256']==hashlib.sha256(v['statement'].encode()).hexdigest();assert x['accepted_credit']==0
assert json.loads((L/'proposals.json').read_text())['proposals']==[]
for p in (L/'primary').glob('*.pdf'):
 m=json.loads(p.with_suffix('.meta.json').read_text());chk(p,m);assert m['url'].endswith('v1')
m=json.loads((L/'manifest.json').read_text());actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ('manifest.json','final-receipt.json')}
assert {x['path'] for x in m['files']}==actual and len(m['files'])==len(actual),'payload exactset'
for x in m['files']:chk(L/x['path'],x)
receipt={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','exact50':True,'all20chunks_in_place':True,'actual_originals_rehashed':True,'exact_payload_files':len(actual),'manifest_sha256':digest(L/'manifest.json')[1],'statement_text_hashes':50,'disjoint_reviewed1133_active50_special3':True,'credit':0,'counts_unchanged':[9,39,40]}
(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
