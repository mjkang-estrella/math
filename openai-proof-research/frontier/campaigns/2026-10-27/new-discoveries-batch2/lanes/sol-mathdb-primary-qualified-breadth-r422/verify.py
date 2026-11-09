import pathlib,json,hashlib,sys,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;R=L/'root-mathdb-breadth-intake-r421';I=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(r):return sha(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())
def check(p,h,n=None):
 assert p.is_file(),str(p)
 assert sha(p.read_bytes())==h,(str(p),'hash')
 if n is not None:assert p.stat().st_size==n,(str(p),'size')
def main():
 for x in load(O/'bindings.json'):check(pathlib.Path(x['original']),x['sha256'],x['size'])
 for x in load(R/'manifest.json')['files']:check(R/x['path'],x['sha256'],x['size'])
 for x in load(R/'bindings.json'):check(pathlib.Path(x['original']),x['sha256'],x['size'])
 chunks=[x for x in load(I/'manifest.json')['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20
 for x in chunks:check(I/x['path'],x['sha256'],x['bytes'])
 for name,targets in [('root-mathdb-accepted-exclusions-r304',{'accepted-exclusions.json','historical-dispositions.json'}),('root-mathdb-cayley-review-intake-r363',{'disposition.json','reserved-ids.json'})]:
  m=load(L/name/'manifest.json');es=m if isinstance(m,list) else m['files'];seen=set()
  for x in es:
   if x['path'] in targets:check(L/name/x['path'],x['sha256']);seen.add(x['path'])
  assert seen==targets,(name,seen)
 reservation=load(R/'reserved-ids.json');ids=reservation['ids'];assert len(ids)==len(set(ids))==50
 assert set(ids)=={x['mathdb_id'] for x in load(R/'queue.json')}
 baseline=load(R/'coverage-delta.json');assert len(baseline)==1933
 assert not set(map(str,ids))&set(baseline)
 assert len(reservation['other_active_reservations'])==50
 assert not set(ids)&set(reservation['other_active_reservations'])
 assert not set(ids)&{372627,372628,368940,404067,364119}
 records={}
 import re
 pattern=re.compile(r'"mathdb_id"\s*:\s*(\d+)')
 for x in chunks:
  with (I/x['path']).open() as f:
   for line in f:
    m=pattern.search(line)
    if m and int(m.group(1)) in ids:
     r=json.loads(line);i=r['mathdb_id'];assert i not in records;records[i]=r
 assert set(records)==set(ids)
 selected=load(O/'selected-records.json');assert len(selected)==50
 assert {r['mathdb_id']:r for r in selected}==records
 ds=load(O/'dispositions.json');assert len(ds)==50;assert {d['mathdb_id'] for d in ds}==set(ids)
 for d in ds:
  r=records[d['mathdb_id']];assert d['literal_statement']==r['statement'];assert d['statement_sha256']==sha(r['statement'].encode());assert d['canonical_record_sha256']==canonical(r)
  assert d['scope'] and d['reason'] and d['evidence_levels']['literal_full_cached_statement_read']
  assert not d['qualified'] and d['credit']==0 and not d['evidence_levels']['current_registry_cleared']
 assert load(O/'proposals.json')==[]
 manifest=load(O/'manifest.json');expected={x['path'] for x in manifest['files']};assert len(expected)==len(manifest['files'])
 excluded={'manifest.json','final-receipt.json'}
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-excluded
 assert actual==expected,{'extra':sorted(actual-expected),'missing':sorted(expected-actual)}
 for x in manifest['files']:check(O/x['path'],x['sha256'],x['size'])
 for x in load(O/'primary-provenance.json'):check(O/x['file'],x['sha256'],x['size'])
 return {'passed':True,'original_bindings':len(load(O/'bindings.json')),'corpus_chunks':20,'exact_assigned_records':50,'baseline':1933,'proposals':0,'payload_files':len(expected),'manifest_sha256':sha((O/'manifest.json').read_bytes()),'mathematical_acceptance':False,'counts_unchanged':{'additional':9,'total':39,'next':40}}
try:
 receipt=main();receipt['verified_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipt['guard_required']='helper_guard.py: 512MiB AS/group RSS; CPU210s; wall230s';(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
except Exception as e:
 (O/'final-receipt.json').write_text(json.dumps({'passed':False,'error':repr(e)},indent=2)+'\n');raise
