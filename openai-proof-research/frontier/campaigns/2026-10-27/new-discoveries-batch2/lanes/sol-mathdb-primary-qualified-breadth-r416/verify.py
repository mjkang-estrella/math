"""Read-only upstream verifier. Only output artifact is lane-local finalreceipt.json."""
import pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r415';C=B/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def digest(p):
 b=p.read_bytes();return hashlib.sha256(b).hexdigest(),len(b)
def check(p,h,n):assert digest(p)==(h,n),str(p)
def canon(x):return json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()
def sh(b):return hashlib.sha256(b).hexdigest()
try:
 refs=j(L/'bindings.json')['references']
 for x in refs:check(pathlib.Path(x['path']),x['sha256'],x['size'])
 for x in j(I/'manifest.json')['files']:check(I/x['path'],x['sha256'],x['size'])
 for x in j(I/'bindings.json'):check(pathlib.Path(x['original']),x['sha256'],x['size'])
 chunks=[x for x in j(C/'manifest.json')['files'] if x['path'].startswith('corpus/') and 'chunk' in x['path']]
 assert len(chunks)==20
 for x in chunks:check(C/x['path'],x['sha256'],x['bytes'])
 r=j(I/'reserved-ids.json');ids=set(r['ids']);q=j(I/'queue.json');cov=j(I/'coverage-delta.json')
 assert len(ids)==len(r['ids'])==50 and ids=={x['mathdb_id'] for x in q}
 assert len(q)==50 and len(cov)==1783
 assert not ids.intersection(map(int,cov)) and not ids.intersection(r['other_active_reservations']) and not ids.intersection([372627,372628,368940])
 rows=j(L/'dispositions.json');recs=j(L/'records.json');assert len(rows)==len(recs)==50 and {x['mathdb_id'] for x in rows}==ids
 original={}
 for c in chunks:
  p=C/c['path']
  for n,line in enumerate(p.open(),1):
   x=json.loads(line)
   if x['mathdb_id'] in ids:
    assert x['mathdb_id'] not in original
    original[x['mathdb_id']]=(str(p),n,x)
 assert set(original)==ids
 for t in recs:
  x=t['record'];p,n,o=original[x['mathdb_id']];assert (t['original'],t['line'],x)==(p,n,o)
 for d in rows:
  p,n,x=original[d['mathdb_id']]
  assert d['original_chunk']==p and d['original_line']==n
  assert d['literal_full_statement']==x['statement'] and d['statement_sha256']==sh(x['statement'].encode())
  assert d['canonical_record_sha256']==sh(canon(x)) and d['canonical_url']==x['canonical_url'] and d['canonical_url_sha256']==sh(x['canonical_url'].encode())
  assert d['scope_quantifiers_and_reason'] and d['evidence_level'] and d['credit']==0
 assert j(L/'proposals.json')==[]
 for p in (L/'evidence').glob('*.provenance.json'):
  x=j(p)
  if 'sha256' in x:check(p.with_name(p.name.replace('.provenance.json','.body')),x['sha256'],x['size'])
 m=j(L/'manifest.json');ex={'manifest.json','finalreceipt.json'}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-ex
 expected={x['path'] for x in m['files']}
 assert len(expected)==len(m['files']) and expected==actual,{'extra':sorted(actual-expected),'missing':sorted(expected-actual)}
 for x in m['files']:check(L/x['path'],x['sha256'],x['size'])
 receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_references':len(refs),'r301_chunks_in_place':20,'assignment_count':50,'reviewed_ids_disjoint':1783,'active_and_special_disjoint':True,'statements_and_canonical_hashes':50,'payload_files':len(actual),'manifest_sha256':digest(L/'manifest.json')[0],'credit':0}
except Exception as e:
 print('VERIFICATION FAIL:',repr(e),file=sys.stderr);sys.exit(1)
(L/'finalreceipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
