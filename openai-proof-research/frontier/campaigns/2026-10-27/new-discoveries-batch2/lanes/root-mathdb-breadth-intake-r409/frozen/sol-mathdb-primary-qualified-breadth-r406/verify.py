"""Separate read-only verifier. No imports from producer scripts; nonzero on any mismatch."""
from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r405';C=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def H(b):return hashlib.sha256(b).hexdigest()
def check(p,r):
 b=p.read_bytes();assert H(b)==r['sha256'],('sha256',str(p));assert len(b)==r.get('size',r.get('bytes')),('size',str(p))
f=load(L/'frozen-references.json');assert len({r['path'] for r in f['references']})==len(f['references'])
for r in f['references']:check(Path(r['path']),r)
for r in load(L/'ancillary-references.json')['references']:check(Path(r['path']),r)
for r in load(I/'manifest.json')['files']:check(I/r['path'],r)
for r in load(I/'bindings.json'):check(Path(r['original']),r);check(I/r['copy'],r)
chunks=[r for r in load(C/'manifest.json')['files'] if r['path'].startswith('corpus/') and r['path'].endswith('.jsonl')];assert len(chunks)==20
assert {str(C/r['path']) for r in chunks}==set(f['corpus_chunks'])
for r in chunks:check(C/r['path'],r)
res=load(I/'reserved-ids.json');ids=set(res['ids']);assert res['lane']==L.name and len(ids)==len(res['ids'])==50
cov=load(I/'coverage-delta.json');assert len(cov)==1533
assert not ids&set(map(int,cov));assert not ids&set(res['other_active_reservations']);assert len(set(res['other_active_reservations']))==50
assert not ids&{372627,372628,368940};assert ids=={r['mathdb_id'] for r in load(I/'queue.json')}
records={}
for r in chunks:
 for line in (C/r['path']).open():
  x=json.loads(line);i=int(x.get('mathdb_id',x.get('id',-1)))
  if i in ids:assert i not in records;records[i]=x
assert set(records)==ids
selected=load(L/'selected-records.json');assert len(selected)==50 and {x['record']['mathdb_id'] for x in selected}==ids
for x in selected:assert x['record']==records[x['record']['mathdb_id']]
for fn in ['statements.json','dispositions.json']:
 a=load(L/fn);assert len(a)==50 and {r['mathdb_id'] for r in a}==ids
 for r in a:
  x=records[r['mathdb_id']];assert r['statement']==x['statement'];assert r['canonical_url']==x['canonical_url'];assert H(x['statement'].encode())==r['statement_sha256'];assert H(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode())==r['canonical_record_sha256']
  if fn=='dispositions.json':assert r['credit']==0 and not r['qualified_brief'] and not r['prior_cleared'] and r['current_registry_status']=='HOLD' and r['record_statement_read']
assert set(load(L/'assessments.json'))==set(map(str,ids));assert load(L/'proposals.json')['qualified_briefs']==[]
for n in ['hayman','abert','stories','integrable','solynin']:
 m=load(L/'primary'/(n+'.meta.json'));check(L/'primary'/m['file'],m)
for n in ['extractions.json','successor-extractions.json']:
 for r in load(L/'primary'/n):check(Path(r['output']),r);assert H(Path(r['input']).read_bytes())==r['input_sha256']
m=load(L/'manifest.json');files={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'};assert files=={r['path'] for r in m['files']};assert len(files)==len(m['files'])
for r in m['files']:check(L/r['path'],r)
print(json.dumps({'status':'PASS','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flat_refs':len(f['references']),'root_manifest_read_only':True,'actual_original_bindings_verified':True,'corpus_chunks':20,'assigned':50,'reviewed_disjoint':1533,'other_active_disjoint':50,'special_ids_disjoint':True,'statement_and_canonical_hashes':50,'payload_exactset':True,'manifest_files':len(files),'manifest_sha256':H((L/'manifest.json').read_bytes()),'qualified_briefs':0,'credit':0,'mathematical_proof_certification':False},indent=2))
