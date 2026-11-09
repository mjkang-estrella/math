"""Read-only independent verification. Run through the fixed helper_guard, python3 -B."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r537';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m,negative=None):
 entries=[dict(e) for e in m['files']];names={e['path'] for e in entries};assert len(names)==len(entries)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('synthetic-unmanifested-file')
 assert actual==names,'exact payload mismatch'
 if negative=='hash':entries[0]['sha256']='0'*64
 if negative=='size':entries[0]['size']+=1
 for e in entries:check(root/e['path'],e)
def main():
 exact(P,j(P/'manifest.json'),sys.argv[1] if len(sys.argv)>1 else None)
 refs=j(P/'flat-bindings.json');assert len({r['path'] for r in refs})==len(refs)
 for r in refs:check(pathlib.Path(r['path']),r)
 check(I/'manifest.json',{'size':12419,'sha256':'a9c103bf1de2a494d49b2669e2076ec456fdd3e8cf4c9bf78eaeb229f7fe24e6'})
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
  assert pathlib.Path(e['original']).read_bytes()==pathlib.Path(e['copy']).read_bytes()
 # Original inventory manifest must explicitly be a bound intake pair.
 assert any(e['original']==str(C/'manifest.json') for e in pairs)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4383
 seen=set();active=j(I/'active-breadth-reservations.json')
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
 assert len(seen)==150
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 q=j(I/'queue.json');ids={r['mathdb_id'] for r in q};res=j(I/'reserved-ids.json');assert res['lane']==P.name and ids==set(res['ids']) and len(q)==len(ids)==50
 ds=j(P/'dispositions.json');ar=j(P/'assigned-records.json');assert len(ds)==len(ar)==50 and {d['mathdb_id'] for d in ds}==ids=={d['mathdb_id'] for d in ar}
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 assert len(found)==50
 for d in ds+ar:
  path,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==path and d['line']==n and d['statement']==r['statement']
  assert d['statement_sha256']==h(r['statement'].encode('utf-8'))
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  if 'record' in d:assert d['record']==r
 for d in ds:assert d['accepted_credit']==0 and d['current_registry_cleared'] is False and d['literal_full_statement_read'] is True
 assert sum(d['disposition']=='EXCLUDE_PUBLIC_SOURCE_RESULT' for d in ds)==5
 assert j(P/'proposals.json')==[]
 for n in ['retrieval-bindings.json','retrieval2-bindings.json']:
  for e in j(P/n):
   if 'failure' not in e:check(P/(e['name']+'.html'),e)
 for n in ['derivative-bindings.json','derivative2-bindings.json']:
  for e in j(P/n):check(pathlib.Path(e['path']),e)
 print(json.dumps({'integrity':'PASS','scientific_acceptance':False,'registry_clearance':False,'literal_reviews':50,'proposals':0,'original_chunks':20,'frozen_inputs':8,'baseline':4383,'direct_pairs':len(pairs),'flat_references':len(refs),'manifest_sha256':h((P/'manifest.json').read_bytes()),'manifest_size':(P/'manifest.json').stat().st_size}))
if __name__=='__main__':main()
