"""Independent read-only verification. Run via the fixed helper_guard.py with python3 -B."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r513';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),'size '+str(p);assert h(b)==e['sha256'],'hash '+str(p)
def exact(p,m,extra=False):
 entries=m['files'];assert len(entries)==len({e['path'] for e in entries}),'duplicate payload'
 actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file()}
 if extra:actual.add('negative-extra-file')
 assert actual-set(m['excluded_exact_paths'])=={e['path'] for e in entries},'extra/missing payload'
 for e in entries:check(p/e['path'],e)
def main():
 m=j(P/'manifest.json')
 if len(sys.argv)>1:
  mode=sys.argv[1];e=m['files'][0]
  if mode=='--negative-hash':e['sha256']='0'*64
  elif mode=='--negative-size':e['size']+=1
  elif mode=='--negative-extra':exact(P,m,extra=True)
  else:raise AssertionError('unknown negative')
  exact(P,m);raise AssertionError('NEGATIVE UNEXPECTEDLY ACCEPTED')
 assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 exact(P,m)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 assert h((I/'manifest.json').read_bytes())=='5b44418b7b4406dd84f4de4154e26ca17cace1e05b99cc1985e193e65fb8a2b3'
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==3883
 res=j(I/'reserved-ids.json');ids=set(res['ids']);q=j(I/'queue.json');assert res['lane']==P.name and len(q)==len(ids)==50 and ids=={r['mathdb_id'] for r in q}
 seen=set()
 for r in j(I/'active-breadth-reservations.json'):
  s=set(r['ids']);assert len(s)==50 and not s&seen and not set(map(str,s))&set(cov) and not s&set(r['protected_ids']);seen|=s
 assert len(seen)==150
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 ds=j(P/'dispositions.json');assigned=j(P/'assigned-records.json');assert len(ds)==len(assigned)==50
 assert {r['mathdb_id'] for r in ds}=={r['mathdb_id'] for r in assigned}==ids
 for a in ds+assigned:
  chunk,n,r=found[a['mathdb_id']];assert (a['corpus_chunk'],a['corpus_line'],a['statement'])==(chunk,n,r['statement'])
  assert a['statement_utf8_sha256']==h(r['statement'].encode('utf-8')) and a['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  if 'record' in a:assert a['record']==r
 for d in ds:assert d['accepted_credit']==0 and d['literal_statement_read'] and not d['current_registry_cleared'] and not d['novelty_pass']
 assert j(P/'proposals.json')==[]
 for name in ['source-bindings.json','successor-bindings.json','derivative-bindings.json','successor-derivative-bindings.json']:
  for e in j(P/name):
   if 'path' in e:check(pathlib.Path(e['path']),e)
 print(json.dumps({'integrity':'PASS','intake_exact':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'chunks_in_place':20,'frozen_inputs':8,'baseline_reported_literal_reviews':3883,'assigned_literal_reviews':50,'proposals':0,'credit':0,'registry':'HOLD','mathematical_or_novelty_pass':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
