#!/usr/bin/env python3
"""Independent read-only integrity verifier. Run via verify.sh (fixed resource guard)."""
import pathlib,json,hashlib,sys,argparse,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r687';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def digest(p):
 h=hashlib.sha256();size=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b);size+=len(b)
 return h.hexdigest(),size
def check(p,e):
 got=digest(p);expected=(e['sha256'],e.get('size',e.get('bytes')))
 if got!=expected:raise ValueError('hash/size mismatch: '+str(p))
def canon(r):return hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')).hexdigest()
def payload(root,m,negative=None):
 expected={e['path']:e for e in m['files']};actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};excluded=set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('injected-extra-file')
 if actual!=set(expected)|excluded:raise ValueError('exact payload mismatch: '+str(actual^(set(expected)|excluded)))
 for name,e in expected.items():
  h,n=digest(root/name)
  if name=='dispositions.json' and negative=='hash':h='0'*64
  if name=='dispositions.json' and negative=='size':n+=1
  if (h,n)!=(e['sha256'],e.get('size',e.get('bytes'))):raise ValueError('payload hash/size mismatch: '+name)
def main():
 args=argparse.ArgumentParser();args.add_argument('--negative-test',choices=['hash','size','extra']);a=args.parse_args()
 m=load(O/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 # Receipt may be absent at first freeze; final run requires it.
 if not (O/'final-verification-receipt.json').exists():raise ValueError('final receipt missing')
 payload(O,m,a.negative_test)
 receipt=load(O/'final-verification-receipt.json')
 assert (receipt['manifest_sha256'],receipt['manifest_size'])==digest(O/'manifest.json'), 'final receipt manifest binding mismatch'
 for e in load(O/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 for e in load(O/'initial-bindings.json')['files']:check(pathlib.Path(e['path']),e)
 im=load(I/'manifest.json');payload(I,im)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
  if pathlib.Path(e['original']).read_bytes()!=pathlib.Path(e['copy']).read_bytes():raise ValueError('direct pair mismatch')
 inv=load(R/'manifest.json');inventory_binding=next(e for e in im['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json');check(R/'manifest.json',inventory_binding)
 chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];frozen=inv['frozen_inputs'];assert len(chunks)==20 and len(frozen)==8
 for e in chunks+frozen:check(R/e['path'],e)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  original=L/'root-mathdb-accepted-exclusions-r304'/name
  assert original.read_bytes()==(R/'frozen/root-mathdb-accepted-exclusions-r304'/name).read_bytes(), 'r304 direct pair mismatch'
 res=load(I/'reserved-ids-r688.json');ids=set(res['ids']);q=load(I/'queue-r688.json');cov=load(I/'coverage-delta.json');assert len(cov)==8083 and len(ids)==50 and ids=={r['mathdb_id'] for r in q}
 protected=set(res['protected_ids']);sets=[set(r['ids']) for r in load(I/'active-breadth-reservations.json')];assert len(sets)==3
 assert ids in sets
 for index,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,cov)) and not s&protected
  for t in sets[index+1:]:assert not s&t
 literals=load(O/'literal-records.json');ds=load(O/'dispositions.json');assert len(literals)==len(ds)==50
 ld={x['record']['mathdb_id']:x for x in literals};dd={x['mathdb_id']:x for x in ds};assert set(ld)==set(dd)==ids
 found={}
 for e in chunks:
  p=R/e['path']
  for n,b in enumerate(p.open('rb'),1):
   r=json.loads(b);id=r.get('mathdb_id',r.get('id'))
   if id in ids:
    assert id not in found;found[id]=(str(p),n,r)
 assert set(found)==ids
 for id,(p,n,r) in found.items():
  x=ld[id];d=dd[id];h=canon(r)
  assert x['corpus_path']==p and x['line']==n and x['record']==r and x['canonical_record_sha256']==h
  assert d['corpus_path']==p and d['corpus_line']==n and d['canonical_record_sha256']==h
  assert d['statement_utf8'].encode('utf-8')==r['statement'].encode('utf-8')
  assert d['statement_utf8_sha256']==hashlib.sha256(r['statement'].encode('utf-8')).hexdigest()
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'}
  assert d['classification_reason'] and d['quantifiers'] and d['technical_disposition'] and d['credit']==0
 proposals=load(O/'proposals.json');assert len(proposals)<=3
 for e in load(O/'source-provenance.json'):
  if 'path' in e:check(O/e['path'],e);assert e['url'].startswith('https://ems.press/') and e['utc']
 for e in load(O/'derivative-bindings.json'):check(O/e['path'],e);assert (O/e['parent']).exists()
 coverage=load(O/'source-coverage.json');from collections import Counter
 assert coverage['classification_counts']==dict(Counter(d['classification'] for d in ds))
 assert coverage['literal_reviews']==50 and coverage['mathdb_requests']==0
 print(json.dumps({'integrity':'PASS','math_novelty':'NOT_PASS','literal_records':50,'corpus_chunks':20,'frozen_inputs':8,'baseline_literal_reviews':8083,'direct_pairs':len(pairs),'proposals':len(proposals),'manifest_sha256':digest(O/'manifest.json')[0],'manifest_size':digest(O/'manifest.json')[1]}))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
