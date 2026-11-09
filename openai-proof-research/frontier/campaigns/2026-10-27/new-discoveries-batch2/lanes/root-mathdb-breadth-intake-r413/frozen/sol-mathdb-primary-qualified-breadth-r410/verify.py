"""Independent read-only input/payload verifier. Writes only this lane's final receipt."""
from pathlib import Path
import hashlib,json,datetime,sys
L=Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r409';C=B/'pi-mathdb-full-corpus-inventory-r301'
H=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,x,sizekey='size'):
 b=p.read_bytes();assert len(b)==x[sizekey],('size',str(p));assert H(b)==x['sha256'],('hash',str(p))
def canon(r):return H(json.dumps({k:v for k,v in r.items() if k!='_chunk'},sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
try:
 refs=load(L/'bindings.json')['references']
 for x in refs:check(Path(x['path']),x)
 root=load(I/'manifest.json')
 for x in root['files']:check(I/x['path'],x)
 for x in load(I/'bindings.json'):
  check(Path(x['original']),x);check(I/x['copy'],x)
 chunks=[x for x in load(C/'manifest.json')['files'] if x['path'].startswith('corpus/')]
 assert len(chunks)==20
 for x in chunks:check(C/x['path'],x,'bytes')
 a=load(I/'reserved-ids.json');ids=set(a['ids']);assert len(ids)==50 and len(a['ids'])==50
 assert not ids.intersection(a['other_active_reservations']) and not ids.intersection({372627,372628,368940})
 reviewed=set(map(int,load(I/'coverage-delta.json')));assert len(reviewed)==1633 and not ids.intersection(reviewed)
 assert ids=={x['mathdb_id'] for x in load(I/'queue.json')}
 original={}
 for f in [C/x['path'] for x in chunks]:
  for line in f.open():
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in original;original[r['mathdb_id']]=(r,str(f))
 assert set(original)==ids
 selected=load(L/'selected-records.json');d=load(L/'dispositions.json')
 assert len(d)==len(selected)==50
 assert {x['mathdb_id'] for x in d}=={x['mathdb_id'] for x in selected}==ids
 for r in selected:
  o,f=original[r['mathdb_id']];assert canon(r)==canon(o) and r['_chunk']==f
 for x in d:
  o,f=original[x['mathdb_id']];assert x['literal_statement']==o['statement'] and x['scope']==o['statement']
  assert x['statement_sha256']==H(o['statement'].encode())
  assert x['canonical_url']==o['canonical_url'] and x['canonical_url_sha256']==H(o['canonical_url'].encode())
  assert x['canonical_record_sha256']==canon(o) and x['corpus_chunk']==f
  assert x['reason'] and x['evidence_level'] and x['credit']==0
  assert x['registry_clearance'].startswith('HOLD')
  e=x['evidence'];m=load(L/e['meta'])
  assert e['source_sha256']==m.get('sha256') and e['url']==m['requested_url']
  if e['text']:assert (L/e['text']).is_file()
 for p in (L/'primary').glob('*.meta.json'):
  m=load(p)
  if 'file' in m:check(L/'primary'/m['file'],m)
 for x in load(L/'primary/extractions.json'):
  assert H((L/'primary'/x['source']).read_bytes())==x['source_sha256']
  assert H((L/'primary'/x['text']).read_bytes())==x['text_sha256']
 assert load(L/'proposals.json')['proposals']==[]
 manifest=load(L/'manifest.json');excluded={'manifest.json','final-receipt.json'}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
 assert manifest['excluded_paths']==sorted(excluded)
 assert actual=={x['path'] for x in manifest['files']}
 for x in manifest['files']:check(L/x['path'],x)
 receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_manifest_read_only':True,'upstream_receipt_writer_invoked':False,'original_refs_verified':len(refs),'root_manifest_files_verified':len(root['files']),'r301_chunks_verified_in_place':20,'assigned_literal_statements_verified':50,'canonical_records_verified':50,'reviewed_ids_disjoint':1633,'active_reservations_disjoint':50,'special_ids_disjoint':[372627,372628,368940],'payload_files_verified':len(actual),'manifest_sha256':H((L/'manifest.json').read_bytes()),'credit':0,'counts_unchanged':{'additional':9,'total':39,'next':40}}
except Exception as e:
 receipt={'status':'FAIL','error':repr(e)};(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');raise
(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
