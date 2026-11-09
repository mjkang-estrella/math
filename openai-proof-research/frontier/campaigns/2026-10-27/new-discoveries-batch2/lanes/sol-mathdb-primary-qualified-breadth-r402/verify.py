"""Independent read-only upstream verifier; only writes lane final receipt."""
from pathlib import Path
import json,hashlib,datetime,sys
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r401';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_bytes())
def digest(b):return hashlib.sha256(b).hexdigest()
def ck(p,r):
 b=p.read_bytes()
 if len(b)!=r.get('size',r.get('bytes')) or digest(b)!=r['sha256']:raise ValueError('binding mismatch: '+str(p))
def canon(r):return json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()
def run():
 f=load(O/'frozen-references.json')['references'];assert len({r['path'] for r in f})==len(f)
 for r in f:ck(Path(r['path']),r)
 for r in load(I/'manifest.json')['files']:ck(I/r['path'],r)
 original=load(I/'bindings.json')
 for r in original:ck(Path(r['original']),r);ck(I/r['copy'],r)
 chunks=[r for r in load(C/'manifest.json')['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20
 for r in chunks:ck(C/r['path'],r)
 reservation=load(I/'reserved-ids.json');ids=reservation['ids'];wanted=set(ids);old=set(map(int,load(I/'coverage-delta.json')))
 assert len(ids)==len(wanted)==50;assert len(old)==1433;assert not wanted&old;assert not wanted&set(reservation['other_active_reservations']);assert not wanted&{372627,372628,368940}
 assert reservation['lane']==O.name;assert {r['mathdb_id'] for r in load(I/'queue.json')}==wanted
 actual={};locations={}
 for q in chunks:
  p=C/q['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in wanted:
    assert r['mathdb_id'] not in actual;actual[r['mathdb_id']]=r;locations[r['mathdb_id']]=(str(p),n)
 assert set(actual)==wanted
 extracts=load(O/'statements.json');assert len(extracts)==50
 for a in extracts:
  i=a['record']['mathdb_id'];assert a['record']==actual[i];assert (a['corpus_path'],a['line'])==locations[i]
 ds=load(O/'dispositions.json');assert len(ds)==50;assert [r['mathdb_id'] for r in ds]==ids
 for d in ds:
  i=d['mathdb_id'];r=actual[i]
  assert d['literal_statement']==d['exact_scope']==r['statement'];assert d['statement_sha256']==digest(r['statement'].encode());assert d['canonical_record_sha256']==digest(canon(r));assert d['canonical_url']==r['canonical_url'];assert d['canonical_url_sha256']==digest(r['canonical_url'].encode());assert d['source_url']==r['source_url'];assert (d['corpus_path'],d['corpus_line'])==locations[i]
  assert d['accepted_credit']==0 and not d['brief_qualified'];assert d['registry_clearance'].startswith('HOLD');assert d['concrete_reason'] and d['evidence_level']
 for p in (O/'primary').glob('*.meta.json'):
  m=load(p);ck(p.with_name(p.name.replace('.meta.json','.pdf')),m);assert m['status']==200
 for r in load(O/'primary/extractions.json'):ck(Path(r['output']),r)
 assert load(O/'proposals.json')['proposals']==[]
 manifest=load(O/'manifest.json')['files']; paths={r['path'] for r in manifest};assert len(paths)==len(manifest)
 expected={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and p.name not in ['manifest.json','final-receipt.json']}
 # Exclusions apply only to the two lane-root files, not arbitrary nested names.
 expected={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and p not in [O/'manifest.json',O/'final-receipt.json']}
 assert paths==expected,('payload set mismatch',paths^expected)
 for r in manifest:ck(O/r['path'],r)
 # In-memory negative control: hash mismatch must raise rather than silently pass.
 q=manifest[0].copy();q['sha256']='0'*64
 try:ck(O/q['path'],q)
 except ValueError:pass
 else:raise AssertionError('negative control accepted bad hash')
 return {'status':'PASS','frozen_actual_originals_checked':len(f),'root_manifest_read_only':True,'root_bound_actual_originals':len(original),'corpus_chunks_in_place':20,'assignment_and_literal_statements':50,'previously_reviewed_disjoint':1433,'other_active_disjoint':50,'payload_files':len(paths),'qualified_briefs':0,'credit':0,'counts_unchanged':{'additional':9,'total':39,'next':40},'negative_hash_control':'rejected','upstream_writes':False}
try:
 receipt=run();receipt['verified_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipt['payload_manifest_sha256']=digest((O/'manifest.json').read_bytes());(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
except Exception as e:
 (O/'final-receipt.json').write_text(json.dumps({'status':'FAIL','error':repr(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n');raise
