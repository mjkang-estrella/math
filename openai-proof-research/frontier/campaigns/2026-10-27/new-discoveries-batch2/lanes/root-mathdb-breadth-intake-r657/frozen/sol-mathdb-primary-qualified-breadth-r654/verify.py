#!/usr/bin/env python3
"""Independent read-only verification. Run only through fixed helper_guard.py."""
from pathlib import Path
import json,hashlib,sys,collections
O=Path(__file__).resolve().parent;B=O.parents[1];I=B/'lanes/root-mathdb-breadth-intake-r653';R=B/'lanes/pi-mathdb-full-corpus-inventory-r301'
def sha(data):return hashlib.sha256(data).hexdigest()
def check(p,d):
 p=Path(p);data=p.read_bytes();assert len(data)==d.get('size',d.get('bytes')),f'size mismatch {p}';assert sha(data)==d['sha256'],f'hash mismatch {p}'
def load(p):return json.loads(Path(p).read_text())
def payload_check(mode=None):
 m=load(O/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 expected={x['path'] for x in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if mode=='extra':actual.add('unexpected-negative-test-payload')
 assert actual==expected,'exact payload mismatch'
 for n,x in enumerate(m['files']):
  data=(O/x['path']).read_bytes()
  if n==0 and mode=='hash':data=bytes([data[0]^1])+data[1:]
  if n==0 and mode=='size':data+=b'!'
  assert len(data)==x['size'],f'size mismatch {x["path"]}'
  assert sha(data)==x['sha256'],f'hash mismatch {x["path"]}'
def verify():
 payload_check()
 for p,d in load(O/'initial-bindings.json').items():check(p,d)
 for p,d in load(O/'flat-bindings.json').items():check(p,d)
 m=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};assert actual=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
 for x in m['files']:check(I/x['path'],x)
 pairs=load(I/'bindings.json')
 for x in pairs:
  check(x['original'],x);check(x['copy'],x);assert Path(x['original']).read_bytes()==Path(x['copy']).read_bytes()
 # Bind inventory itself to intake's declared pair, then verify in-place paths.
 invpair=[x for x in pairs if x['original']==str(R/'manifest.json')];assert len(invpair)==1
 check(R/'manifest.json',invpair[0]);inv=load(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for x in chunks+inv['frozen_inputs']:check(R/x['path'],x)
 cov=load(I/'coverage-delta.json');assert len(cov)==7233,len(cov)
 active=load(I/'active-breadth-reservations.json');assert len(active)==3;seen=set();covered={int(k) for k in cov}
 for r in active:
  ids=set(r['ids']);assert len(ids)==len(r['ids'])==50
  assert not ids & covered;assert not ids & seen;assert not ids & set(r['protected_ids']);assert not ids & set(r['active_hypothesis_ids']);seen|=ids
 res=load(I/'reserved-ids-r654.json');ids=set(res['ids']);assert res['coverage_baseline']==7233
 own=[r for r in active if r['lane']==O.name];assert len(own)==1 and set(own[0]['ids'])==ids
 q=load(I/'queue-r654.json');assert len(q)==50 and {r['mathdb_id'] for r in q}==ids
 rows=load(O/'literal-records.json');ds=load(O/'dispositions.json');assert len(rows)==len(ds)==50
 assert {x['record']['mathdb_id'] for x in rows}==ids=={d['mathdb_id'] for d in ds}
 byid={d['mathdb_id']:d for d in ds};groups=collections.defaultdict(dict)
 for x in rows:groups[x['chunk']][x['line']]=x
 for path,lines in groups.items():
  assert path in {str(R/x['path']) for x in chunks}
  found=set()
  for n,line in enumerate(Path(path).open(),1):
   if n not in lines:continue
   x=lines[n];r=json.loads(line);assert r==x['record'];k=r['mathdb_id'];d=byid[k]
   canon=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
   assert canon==x['canonical_sha256']==d['canonical_record_sha256'];assert d['statement']==r['statement'];assert d['statement_utf8_sha256']==sha(r['statement'].encode());assert d['corpus_chunk']==path and d['corpus_line']==n
   assert d['completeness_classification'] in {'complete','incomplete','scope-ambiguous','definition-dependent'};assert all(d[k] for k in ['completeness_reason','literal_quantifiers','technical_assessment']);assert d['credit']==0 and not d['prior_cleared'];found.add(n)
  assert found==set(lines)
 assert len(load(O/'proposals.json'))<=3;assert load(O/'proposals.json')==[]
 for x in load(O/'source-provenance.json'):
  if 'path' in x:check(O/x['path'],x)
 x=load(O/'image-binding.json');check(O/x['path'],x)
 return {'integrity':'PASS','literal_reviews':50,'baseline':7233,'original_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(pairs),'reservation_sets':len(active),'classification_counts':dict(collections.Counter(d['completeness_classification'] for d in ds)),'proposals':0,'scientific_acceptance':False,'registry':'HOLD'}
if __name__=='__main__':
 try:
  if len(sys.argv)>1:
   mode=sys.argv[1];assert mode in ['hash','size','extra'];payload_check(mode);raise RuntimeError('negative mutation accepted')
  print(json.dumps(verify(),sort_keys=True))
 except Exception as e:
  print(f'VERIFICATION FAILED: {type(e).__name__}: {e}',file=sys.stderr);sys.exit(1)
