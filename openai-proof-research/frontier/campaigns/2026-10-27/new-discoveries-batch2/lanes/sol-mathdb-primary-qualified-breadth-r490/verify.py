"""Independent read-only byte/assignment verifier; no upstream code execution."""
from pathlib import Path
import json,hashlib,sys
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r489';C=L/'pi-mathdb-full-corpus-inventory-r301'
def get(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def ck(p,r):
 b=p.read_bytes();assert len(b)==r.get('size',r.get('bytes')),('size',str(p));assert digest(b)==r['sha256'],('digest',str(p))
def exact(root,m):
 names=[r['path'] for r in m['files']];assert len(names)==len(set(names));assert set(m['excluded_exact_paths'])==({'manifest.json','final-receipt.json'} if root==O else {'manifest.json','verification-receipt.json'})
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual==set(names),('membership',actual^set(names))
 for r in m['files']:ck(root/r['path'],r)
def main():
 m=get(O/'manifest.json')
 if '--negative-membership' in sys.argv:m['files']=m['files'][:-1]
 exact(O,m);exact(I,get(I/'manifest.json'))
 for r in get(I/'bindings.json'):
  ck(Path(r['original']),r);ck(Path(r['copy']),r)
 for n in ['initial-flat-bindings.json','flat-bindings.json','pinned-admin-bindings.json']:
  for r in get(O/n):ck(Path(r['path']),r)
 cm=get(C/'manifest.json');chunks=[r for r in cm['files'] if r['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20;assert len(cm['frozen_inputs'])==8
 for r in chunks+cm['frozen_inputs']:ck(C/r['path'],r)
 q=get(I/'queue.json');reserved=get(I/'reserved-ids.json');ids=set(reserved['ids']);assert len(ids)==len(reserved['ids'])==len(q)==50;assert ids=={r['mathdb_id'] for r in q}
 a=get(I/'frozen/root-mathdb-breadth-intake-r479/reserved-ids.json');b=get(I/'frozen/root-mathdb-breadth-intake-r487/reserved-ids.json');assert a['lane']=='claude-mathdb-primary-qualified-breadth-r480';assert b['lane']=='sol-mathdb-primary-qualified-breadth-r488';aa=set(a['ids']);bb=set(b['ids']);assert len(aa)==len(bb)==50 and not aa&bb;assert aa|bb==set(reserved['other_active_reservations']);assert len(reserved['other_active_reservations'])==100 and not ids&(aa|bb)
 assert not ids&{372627,372628,368940,404067,364119};assert get(I/'adjudications.json')['372627']['credit']==0
 cov=get(I/'coverage-delta.json');assert len(cov)==3483 and not ids&set(map(int,cov))
 ds=get(O/'dispositions.json');ar=get(O/'assigned-records.json');assert len(ds)==len(ar)==50;assert {x['mathdb_id'] for x in ds}==ids;assert len({x['mathdb_id'] for x in ds})==50;assert {x['record']['mathdb_id'] for x in ar}==ids
 if '--negative-literal' in sys.argv:ds[0]['literal_statement']+=' altered'
 amap={x['record']['mathdb_id']:x for x in ar};bychunk={}
 for d in ds:bychunk.setdefault(d['original_chunk'],[]).append(d)
 for path,items in bychunk.items():
  assert path in {str(C/r['path']) for r in chunks}; wanted={d['original_line']:d for d in items};seen=set()
  for line,z in enumerate(Path(path).open(),1):
   if line not in wanted:continue
   r=json.loads(z);d=wanted[line];id=d['mathdb_id'];assert r['mathdb_id']==id;assert amap[id]['record']==r;assert amap[id]['original_chunk']==path and amap[id]['original_line']==line
   assert r['statement']==d['literal_statement'];assert digest(r['statement'].encode('utf8'))==d['statement_utf8_sha256'];assert digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))==d['canonical_record_sha256'];assert d['accepted_credit']==0;assert d['technical_reason'];seen.add(line)
  assert seen==set(wanted)
 for r in get(O/'source-bindings.json'):
  assert r['mathdb_id'] in ids and r['result']=='retained';ck(Path(r['pdf']['path']),r['pdf']);ck(Path(r['text']['path']),r['text'])
 assert len(get(O/'source-bindings.json'))==50;assert get(O/'proposals.json')==[]
 c=get(O/'coverage.json');assert c['this_lane_individual_literal_reviews']==50 and c['baseline_reported_literal_reviews']==3483;assert c['counts']==dict(additional=9,total=39,next=40)
 print(json.dumps(dict(integrity='PASS',assigned=50,other_reserved=100,chunks=20,frozen_inputs=8,payloads=len(m['files']),mathematics_and_novelty='NOT CERTIFIED')))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
