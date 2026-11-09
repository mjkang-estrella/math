"""Read-only upstream verification; only writes this lane's final receipt."""
import pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r407';C=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert sha(b)==e['sha256'],('sha',str(p))
def canonical(r):return sha(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
def verify():
 bindings=load(L/'bindings.json')
 for e in bindings['references']:check(pathlib.Path(e['path']),e)
 for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):check(pathlib.Path(e['original']),e)
 chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
 assert len(chunks)==20 and set(bindings['corpus_chunks'])=={str(C/e['path']) for e in chunks}
 for e in chunks:check(C/e['path'],e)
 res=load(I/'reserved-ids.json');ids=set(res['ids']);reviewed=set(map(int,load(I/'coverage-delta.json')))
 assert len(res['ids'])==len(ids)==50 and len(reviewed)==1583
 assert not ids&reviewed and not ids&set(res['other_active_reservations']) and len(res['other_active_reservations'])==50
 assert not ids&{372627,372628,368940}
 queue=load(I/'queue.json');assert len(queue)==50 and {x['mathdb_id'] for x in queue}==ids
 q={x['mathdb_id']:x for x in queue}
 originals={}
 for e in chunks:
  with (C/e['path']).open() as f:
   for line in f:
    r=json.loads(line);k=r.get('mathdb_id',r.get('id'))
    if k in ids:
     assert k not in originals;originals[k]=(r,sha(line.encode()),str(C/e['path']))
 assert set(originals)==ids
 records=load(L/'records.json');assert len(records)==50 and {x['record']['mathdb_id'] for x in records}==ids
 for x in records:
  k=x['record']['mathdb_id'];r,h,p=originals[k];assert x['record']==r and x['line_sha256']==h and x['corpus_path']==p
 d=load(L/'dispositions.json');assert len(d)==50 and {x['mathdb_id'] for x in d}==ids
 for x in d:
  r,h,p=originals[x['mathdb_id']]
  assert x['literal_statement']==x['full_scope_and_quantifiers']==r['statement']
  assert x['statement_sha256']==sha(r['statement'].encode()) and x['canonical_record_sha256']==canonical(r)
  assert x['canonical_url']==r['canonical_url']==q[r['mathdb_id']]['canonical_url']
  assert x['canonical_url_sha256']==sha(r['canonical_url'].encode()) and x['corpus_line_sha256']==h and x['corpus_path']==p
  assert x['accepted_credit']==0 and x['reason'] and x['evidence_level'] and not x['prior_cleared']
 assert load(L/'proposals.json')==[]
 for e in load(L/'source-provenance.json'):
  if 'path'in e:check(L/e['path'],e)
 assessment=[int(line.split('\t',1)[0]) for line in (L/'assessment.tsv').read_text().splitlines()]
 assert len(assessment)==50 and set(assessment)==ids
 m=load(L/'manifest.json');paths=[e['path'] for e in m['files']];excluded={'manifest.json','finalreceipt.json'}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
 assert len(paths)==len(set(paths)) and set(paths)==actual
 for e in m['files']:
  assert not pathlib.Path(e['path']).is_absolute() and '..' not in pathlib.Path(e['path']).parts
  check(L/e['path'],e)
 return {'status':'PASS','flat_original_references':len(bindings['references']),'corpus_chunks_verified_in_place':20,'assigned':50,'dispositions':50,'reviewed_disjoint':1583,'other_active_disjoint':50,'retained_source_bodies':sum('path'in e for e in load(L/'source-provenance.json')),'manifest_payload_files':len(paths),'payload_exactset':True,'proposals':0,'credit_change':0,'additional':9,'total':39,'next':40,'upstream_writes':0}
try:receipt=verify()
except Exception as e:
 receipt={'status':'FAIL','error':repr(e)};code=1
else:code=0
receipt['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(L/'finalreceipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));sys.exit(code)
