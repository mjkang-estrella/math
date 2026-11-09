"""Read-only independent integrity checks. Never imports/runs an upstream verifier."""
import pathlib,json,hashlib,sys,copy
W=pathlib.Path(__file__).resolve().parent;L=W.parent;I=L/'root-mathdb-circulant-13-prior-adjudication-r481';C=L/'pi-mathdb-full-corpus-inventory-r301'
def H(b):return hashlib.sha256(b).hexdigest()
def J(p):return json.loads(p.read_text())
def check(p,r):
 b=p.read_bytes();assert len(b)==r.get('size',r.get('bytes')) and H(b)==r['sha256'],str(p)
def exact(base,m,excluded):
 expected={r['path'] for r in m['files']};actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}-set(excluded)
 assert len(expected)==len(m['files']) and expected==actual,('payload-set',expected^actual)
 for r in m['files']:check(base/r['path'],r)
def rowcheck(r,record):
 assert r['original_literal_statement']==record['statement']
 assert r['statement_utf8_sha256']==H(record['statement'].encode())
 assert r['canonical_record_sha256']==H(json.dumps(record,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
 assert r['accepted_credit']==0

def main():
 rows=J(W/'dispositions.json'); own=J(I/'reserved-ids-r484.json');q=J(I/'queue-r484.json');other=J(I/'reserved-ids.json');claude=J(L/'root-mathdb-breadth-intake-r479/reserved-ids.json')
 ids=set(own['ids']);o=set(other['ids']);c=set(claude['ids'])
 assert own['lane']==W.name and len(ids)==len(rows)==len(q)==50
 assert set(r['mathdb_id'] for r in rows)==ids=={r['mathdb_id'] for r in q}
 assert len(o)==len(c)==50 and not(o&c) and not(ids&(o|c)) and set(own['other_active_reservations'])==o|c
 assert not ids&{372627,372628,368940,404067,364119}
 baseline=J(I/'coverage-delta.json');assert len(baseline)==3333 and not ids&{int(k) for k in baseline}
 exact(I,J(I/'manifest.json'),['manifest.json','verification-receipt.json'])
 direct=J(I/'bindings.json')
 for r in direct:
  check(pathlib.Path(r['original']),r);check(pathlib.Path(r['copy']),r)
 cm=J(C/'manifest.json');chunks=[r for r in cm['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for r in chunks+cm['frozen_inputs']:check(C/r['path'],r)
 for name in ['flat-bindings.json','source-bindings.json','supplemental-bindings.json']:
  for r in J(W/name):
   check(pathlib.Path(r['path']),r)
   if 'copy' in r:check(pathlib.Path(r['copy']),r)
 for name in ['sources.jsonl','successor-sources.jsonl']:
  for line in (W/name).read_text().splitlines():
   r=json.loads(line)
   if 'path'in r:check(pathlib.Path(r['path']),r)
 originals={}
 wanted={r['original_chunk'] for r in rows}
 for chunk in wanted:
  for line_no,s in enumerate(pathlib.Path(chunk).open(),1):
   record=json.loads(s)
   if record['mathdb_id'] in ids:originals[record['mathdb_id']]=(chunk,line_no,record)
 assert set(originals)==ids
 for r in rows:
  p,n,record=originals[r['mathdb_id']];assert r['original_chunk']==p and r['original_line']==n
  rowcheck(r,record)
 assert J(W/'proposals.json')==[]
 if '--negative' in sys.argv:
  caught=[]
  bad=copy.deepcopy(rows[0]);bad['statement_utf8_sha256']='0'*64
  try:rowcheck(bad,originals[bad['mathdb_id']][2])
  except AssertionError:caught.append('statement hash mutation rejected')
  bad=copy.deepcopy(rows[0]);bad['canonical_record_sha256']='0'*64
  try:rowcheck(bad,originals[bad['mathdb_id']][2])
  except AssertionError:caught.append('canonical record mutation rejected')
  r={'sha256':'0'*64,'size':(W/'verify.py').stat().st_size}
  try:check(W/'verify.py',r)
  except AssertionError:caught.append('binding mutation rejected')
  m={'files':[{'path':'verify.py','sha256':H((W/'verify.py').read_bytes()),'size':(W/'verify.py').stat().st_size}]}
  try:exact(W,m,['manifest.json','final-receipt.jsonl'])
  except AssertionError:caught.append('incomplete payload manifest rejected')
  assert len(caught)==4
  print(json.dumps({'bounded_negative_test':'PASS','mutations':caught}));return
 exact(W,J(W/'manifest.json'),['manifest.json','final-receipt.jsonl'])
 print(json.dumps({'integrity':'PASS','own_assignment':'queue-r484.json / reserved-ids-r484.json','literal_rows':50,'other_reservations':[{'lane':other['lane'],'count':50},{'lane':claude['lane'],'count':50}],'baseline':3333,'corpus_chunks_in_place':20,'frozen_inputs_separately_checked':8,'direct_bindings_checked':len(direct),'payload_count':len(J(W/'manifest.json')['files']),'mathematics_pass':False,'novelty_pass':False,'accepted_credit':0}))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(json.dumps({'integrity':'FAIL','error':repr(e)}));sys.exit(1)
