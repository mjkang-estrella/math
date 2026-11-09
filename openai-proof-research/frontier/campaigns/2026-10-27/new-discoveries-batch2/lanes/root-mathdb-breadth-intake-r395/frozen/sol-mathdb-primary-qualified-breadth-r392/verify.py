import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent;R=B/'root-mathdb-breadth-intake-r391';I=B/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def check(p,e):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 assert h.hexdigest()==e['sha256'] and n==e.get('size',e.get('bytes')),str(p)
refs=j(L/'input-bindings.json')['refs'];assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(pathlib.Path(e['path']),e)
for e in j(R/'manifest.json')['files']:check(R/e['path'],e)
chunks=[e for e in j(I/'manifest.json')['files'] if e['path'].startswith('corpus/') and e['path'].endswith('.jsonl')];assert len(chunks)==20
for e in chunks:check(I/e['path'],e)
r=j(R/'reserved-ids.json');ids=set(r['ids']);old=j(R/'coverage-delta.json');other=set(r['other_active_reservations'])
assert r['lane']==L.name and len(r['ids'])==len(ids)==50 and len(old)==1183 and len(other)==50
assert not ids&set(map(int,old)) and not ids&other and not ids&{372627,372628,368940}
rs=j(L/'records.json');ds=j(L/'dispositions.json');assert len(rs)==len(ds)==50
assert {x['mathdb_id'] for x in ds}=={x['mathdb_id'] for x in rs}==ids
actual={}
for e in chunks:
 with (I/e['path']).open() as f:
  for line in f:
   x=json.loads(line)
   if x.get('mathdb_id') in ids:
    assert x['mathdb_id'] not in actual;actual[x['mathdb_id']]=x
assert len(actual)==50
for d in ds:
 x=actual[d['mathdb_id']];assert x==next(r for r in rs if r['mathdb_id']==d['mathdb_id'])
 assert d['literal_statement']==x['statement']
 assert hashlib.sha256(x['statement'].encode()).hexdigest()==d['literal_sha256']
 assert hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()==d['canonical_record_sha256']
 assert d['exact_quantifiers_and_scope'] and d['concrete_reason'] and d['accepted_credit']==0
assert j(L/'proposals.json')==[]
for e in j(L/'successor-provenance.json'):
 if 'file' in e:check(L/e['file'],e)
mandatory=[B/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]+[B/'root-mathdb-cayley-review-intake-r363/disposition.json']
assert all(str(p) in {e['path'] for e in refs} for p in mandatory)
manifest=j(L/'manifest.json')['files'];names={e['path'] for e in manifest}
actual_names={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','final-receipt.json']}
assert len(names)==len(manifest) and names==actual_names,(names^actual_names)
for e in manifest:check(L/e['path'],e)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','frozen_actual_refs':len(refs),'corpus_chunks_in_place':20,'literal_and_canonical_records':50,'reviewed_exclusion_count':1183,'other_active_reservations':50,'exact_payload_files':len(names),'science_or_novelty_certified':False}
(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
