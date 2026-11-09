"""Independent read-only verifier. Run with python3 -B under the fixed helper guard."""
import pathlib,json,hashlib,sys,collections
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r719';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def req(x,msg):
 if not x:raise ValueError(msg)
def check(p,e):
 req(p.is_file() and not p.is_symlink(),'missing/symlink '+str(p));b=p.read_bytes();req(len(b)==e.get('size',e.get('bytes')),'size '+str(p));req(h(b)==e['sha256'],'hash '+str(p))
def exact(root,m):
 names=[e['path'] for e in m['files']];req(len(names)==len(set(names)),'duplicate paths');actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};req(actual-set(m['excluded_exact_paths'])==set(names),'extra/missing payload')
 for e in m['files']:check(root/e['path'],e)
def main():
 m=j(P/'manifest.json');req(set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'},'exclusions')
 if len(sys.argv)>1:
  mode=sys.argv[1];req(mode in ['--negative-hash','--negative-size','--negative-extra'],'argument')
  if mode=='--negative-hash':m['files'][0]['sha256']='0'*64
  if mode=='--negative-size':m['files'][0]['size']+=1
  if mode=='--negative-extra':m['files']=m['files'][1:] # one real payload becomes unlisted extra
 exact(P,m)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];req(len(chunks)==20 and len(cm['frozen_inputs'])==8,'20/8')
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');req(len(cov)==8883,'coverage');seen=set();active=j(I/'active-breadth-reservations.json');req(len(active)==3,'reservations')
 for a in active:
  ids=set(a['ids']);req(len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']),'disjointness');seen|=ids
 req(len(seen)==150,'150');req(any('r628' in a['lane'] and 'held' in a['status'].lower() for a in active),'held');req(any('r718' in a['lane'] for a in active),'r718')
 res=j(I/'reserved-ids-r720.json');ids=set(res['ids']);queue=j(I/'queue-r720.json');req(len(queue)==50 and {r['mathdb_id'] for r in queue}==ids,'queue')
 ds=j(P/'dispositions.json');lits=j(P/'literal-records.json');req(len(ds)==len(lits)==50 and {d['mathdb_id'] for d in ds}==ids,'exact50');req(len({d['mathdb_id'] for d in ds})==50,'duplicate')
 by={e['record']['mathdb_id']:e for e in lits};found={}
 # Stream in place; emit no adjacent content.
 for e in chunks:
  p=C/e['path']
  with p.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in ids:
     req(r['mathdb_id'] not in found,'corpus duplicate');found[r['mathdb_id']]=(e['path'],n,r)
 req(set(found)==ids,'source set')
 for d in ds:
  i=d['mathdb_id'];ck,n,r=found[i];req(d['corpus_chunk']==ck and d['corpus_line']==n,'locator');req(by[i]['record']==r and by[i]['corpus_chunk']==ck and by[i]['corpus_line']==n,'literal record')
  req(d['exact_utf8_statement']==r['statement'],'statement');req(d['statement_utf8_sha256']==h(r['statement'].encode('utf-8')),'UTF8 hash');ch=h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'));req(d['canonical_record_sha256']==by[i]['canonical_record_sha256']==ch,'canonical hash')
  req(d['classification'] in ['complete','incomplete','definition-dependent','scope-ambiguous'] and bool(d['classification_reason_and_quantifiers']) and bool(d['technical_assessment']),'classification');req(d['complete_mathematical_statement_reviewed']==(d['classification']=='complete'),'complete flag');req(d['accepted_credit']==0 and not d['current_registry_cleared'] and not d['replaced'],'gates')
 req(j(P/'proposals.json')==[],'zero proposals');counts=dict(collections.Counter(d['classification'] for d in ds));req(j(P/'source-coverage.json')['classifications']==counts,'coverage categories')
 for s in j(P/'source-provenance.json'):
  for typ in ['pdf','text']:check(P/s[typ+'_path'],{'size':s[typ+'_size'],'sha256':s[typ+'_sha256']})
 return {'integrity':'PASS','literal_reviews':50,'classification_counts':counts,'chunks_in_place':20,'frozen_inputs':8,'direct_original_copy_pairs':49,'baseline_literal_reviews':8883,'reservations':150,'proposals':0,'math_and_novelty':'NOT_CERTIFIED; current registry HOLD'}
try:print(json.dumps(main(),sort_keys=True))
except Exception as e:print(json.dumps({'integrity':'FAIL','reason':str(e)}));sys.exit(1)
