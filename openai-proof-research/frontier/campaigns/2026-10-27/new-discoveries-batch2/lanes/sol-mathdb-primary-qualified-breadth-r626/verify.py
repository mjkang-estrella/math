"""Independent read-only verifier. Run through fixed helper_guard.py; no upstream execution."""
from pathlib import Path
import json,hashlib,sys,argparse
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r625'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,x):
 b=p.read_bytes()
 assert len(b)==x.get('size',x.get('bytes')),'size mismatch: '+str(p)
 assert digest(b)==x['sha256'],'hash mismatch: '+str(p)
 return b
def exact(root,m,negative=None):
 names={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 expected={x['path'] for x in m['files']}
 assert len(expected)==len(m['files']),'duplicate manifest paths'
 excluded=set(m['excluded_exact_paths'])
 if negative=='extra': names.add('__in_memory_extra__')
 assert names-excluded==expected,'exact payload mismatch'
 for x in m['files']:check(root/x['path'],x)
def run(negative=None):
 m=load(D/'manifest.json')
 assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 if negative=='hash':m['files'][0]['sha256']='0'*64
 if negative=='size':m['files'][0]['size']+=1
 exact(D,m,negative)
 refs=load(D/'flat-bindings.json')
 for x in refs:check(Path(x['path']),x)
 assert digest((I/'manifest.json').read_bytes())=='db41d16843b88e3f88a803283128dba18df4e5cab5497964f4eb5e41500755fc'
 assert (I/'manifest.json').stat().st_size==10061
 exact(I,load(I/'manifest.json'))
 for x in load(I/'bindings.json'):
  a=check(Path(x['original']),x);b=check(Path(x['copy']),x);assert a==b
 cm=load(C/'manifest.json'); chunks=[x for x in cm['files'] if x['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for x in chunks+cm['frozen_inputs']:check(C/x['path'],x)
 cov=load(I/'coverage-delta.json');assert len(cov)==6583
 covered=set(map(int,cov)); active=load(I/'active-breadth-reservations.json')
 allsets=[]
 for a in active:
  s=set(a['ids']);assert len(s)==len(a['ids'])==50
  assert not s&covered and not s&set(a['protected_ids']) and not s&set(a['other_active_reservations'])
  allsets.append(s)
 for n,s in enumerate(allsets):
  for t in allsets[n+1:]:assert not s&t
 reserve=load(I/'reserved-ids-r626.json')
 ids=set(reserve['ids']);q=load(I/'queue-r626.json')
 assert len(ids)==len(q)==50 and ids=={r['mathdb_id'] for r in q}
 assert ids==next(s for a,s in zip(active,allsets) if a['lane']==D.name)
 assert reserve['coverage_baseline']==6583
 assert not ids&{338366,338408}
 focus=load(I/'focused-assignment.json')
 assert focus['mathdb_id']==338366 and focus['lane']=='claude-mathdb-curvature-prior-review-r618'
 a=load(I/'adjudications.json')
 for i in ['338290','339564','372627']:assert a[i]['credit']==0
 assert a['337963']['disposition'].startswith('PARK')
 literals=load(D/'literal-records.json'); dispositions=load(D/'dispositions.json')
 assert len(literals)==len(dispositions)==50
 assert {x['record']['mathdb_id'] for x in literals}==ids
 assert {x['mathdb_id'] for x in dispositions}==ids
 observed={}
 for x in chunks:
  path=C/x['path']
  for n,line in enumerate(path.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:observed[r['mathdb_id']]=(r,str(path),n)
 assert set(observed)==ids
 byid={x['mathdb_id']:x for x in dispositions}
 for x in literals:
  r=x['record'];id=r['mathdb_id'];orig,path,n=observed[id]
  assert orig==r and path==x['corpus_path'] and n==x['line']
  h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  sh=digest(r['statement'].encode('utf-8'))
  d=byid[id]
  assert h==x['canonical_record_sha256']==d['canonical_record_sha256']
  assert sh==x['statement_utf8_sha256']==d['statement_utf8_sha256']
  assert r['statement']==d['statement'] and d['corpus_path']==path and d['corpus_line']==n
  assert d['corpus_statement_completeness']==r['statement_completeness']
  assert d['independent_scope_classification'] in {'complete','incomplete','definition-dependent','scope-ambiguous'}
  assert d['literal_record_review'] and d['accepted_credit']==0 and not d['prior_cleared']
  assert d['quantifiers_route_objection']
 assert load(D/'proposals.json')==[]
 for e in load(D/'fetch-provenance.json'):
  assert e['url'].startswith('https://arxiv.org/html/')
  check(D/e['path'],e)
 for e in load(D/'derivative-bindings.json'):check(D/e['path'],e)
 return {'status':'INTEGRITY_PASS_ONLY','records':50,'baseline':6583,'original_chunks':20,'frozen_inputs':8,'direct_pairs':len(load(I/'bindings.json')),'flat_bindings':len(refs),'proposal_count':0,'manifest_sha256':digest((D/'manifest.json').read_bytes()),'manifest_size':(D/'manifest.json').stat().st_size}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--negative',choices=['hash','size','extra']);args=p.parse_args()
 try:
  result=run(args.negative)
  assert args.negative is None,'negative test unexpectedly passed'
  print(json.dumps(result))
 except Exception as e:
  print(json.dumps({'status':'FAIL','error':str(e),'negative':args.negative}));sys.exit(1)
