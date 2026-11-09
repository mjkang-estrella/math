"""Read-only independent integrity verifier. Run via verify.sh, under fixed guard."""
import hashlib,json,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
L=P.parent
I=L/'root-mathdb-breadth-intake-r663'
C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}'
 assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m,extra=False):
 assert len(m['files'])==len({e['path'] for e in m['files']})
 actual={str(f.relative_to(root)) for f in root.rglob('*') if f.is_file()}
 if extra:actual.add('injected-extra-file')
 assert actual-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']},f'exact payload mismatch: {root}'
 for e in m['files']:check(root/e['path'],e)
def main():
 if '--negative-hash' in sys.argv:
  b=(P/'SUMMARY.md').read_bytes();check(P/'SUMMARY.md',{'size':len(b),'sha256':'0'*64});raise RuntimeError('negative accepted')
 if '--negative-size' in sys.argv:
  b=(P/'SUMMARY.md').read_bytes();check(P/'SUMMARY.md',{'size':len(b)+1,'sha256':h(b)});raise RuntimeError('negative accepted')
 if '--negative-extra' in sys.argv:exact(P,j(P/'manifest.json'),True);raise RuntimeError('negative accepted')
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
 for e in j(P/'initial-bindings.json')+j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 assert (C/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==7483
 active=j(I/'active-breadth-reservations.json');seen=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 assert len(active)==3 and len(seen)==150
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 res=j(I/'reserved-ids-r664.json');ids=set(res['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r664.json')}
 assert next(a for a in active if a['lane']==P.name)['ids']==res['ids']
 literals=j(P/'literal-records.json');ds=j(P/'dispositions.json');assert len(ds)==len(literals)==50 and {d['mathdb_id'] for d in ds}==ids
 assert len({d['mathdb_id'] for d in ds})==50
 check(P/'literal-records.json',j(P/'literal-binding.json'))
 found={}
 for e in chunks:
  f=C/e['path']
  for n,line in enumerate(f.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(f.resolve()),n,r)
 assert len(found)==50
 lm={x['record']['mathdb_id']:x for x in literals}
 for d in ds:
  path,n,r=found[d['mathdb_id']];x=lm[d['mathdb_id']]
  assert x['record']==r and d['statement']==r['statement']
  for q in [d,x]:
   assert q['corpus_chunk']==path and q['corpus_line']==n
   assert q['statement_utf8_sha256']==h(r['statement'].encode())
   assert q['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['independent_completeness'] in {'complete','definition-dependent','scope-ambiguous','incomplete'} and d['completeness_reason'] and d['technical_assessment']
  assert d['accepted_credit']==0 and d['current_registry_cleared'] is False
 assert j(P/'proposals.json')==[]
 for file in ['source-provenance.json','derivative-bindings.json']:
  for e in j(P/file):
   if 'file' in e:check(P/e['file'],e)
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'baseline':7483,'original_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(pairs),'disjoint_reserved_sets':3,'proposals':0,'scientific_acceptance':False}))
if __name__=='__main__':main()
