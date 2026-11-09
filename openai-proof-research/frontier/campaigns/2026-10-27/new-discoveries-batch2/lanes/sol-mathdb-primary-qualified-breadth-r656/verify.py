"""Read-only independent verifier. Always invoke via verify.sh / fixed guard."""
import pathlib,json,hashlib,sys,subprocess
P=pathlib.Path(__file__).resolve().parent
I=P.parent/'root-mathdb-breadth-intake-r655'
R=P.parent/'pi-mathdb-full-corpus-inventory-r301'
def digest(p):
 b=pathlib.Path(p).read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):assert digest(p)=={'sha256':e['sha256'],'size':e.get('size',e.get('bytes'))},str(p)
def load(p):return json.loads(pathlib.Path(p).read_text())
def canonical(r):return hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def main():
 m=load(P/'manifest.json');names={x['path'] for x in m['files']};actual={str(x.relative_to(P)) for x in P.rglob('*') if x.is_file()}-{'manifest.json','final-verification-receipt.json'}
 assert len(names)==len(m['files'])
 mode=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 if mode=='extra':actual.add('synthetic-unlisted-file')
 if mode=='hash':m['files'][0]['sha256']='0'*64
 if mode=='size':m['files'][0]['size']+=1
 assert names==actual,'extra/missing payload'
 for e in m['files']:check(P/e['path'],e)
 for n in ['bootstrap-bindings.json','flat-bindings.json']:
  for path,e in load(P/n).items():check(path,e)
 im=load(I/'manifest.json');inames={x['path'] for x in im['files']};iactual={str(x.relative_to(I)) for x in I.rglob('*') if x.is_file()}-{'manifest.json','verification-receipt.json'}
 assert inames==iactual
 for e in im['files']:check(I/e['path'],e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(e['original'],e);check(e['copy'],e)
 rm=load(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 # Verify the actual r301 inventory manifest equals its intake-bound copy.
 frozen=I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'
 assert digest(R/'manifest.json')==digest(frozen)
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 reserve=load(I/'reserved-ids-r656.json');ids=reserve['ids'];queue=load(I/'queue-r656.json');coverage=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
 assert len(ids)==len(set(ids))==50 and set(ids)=={x['mathdb_id'] for x in queue}
 assert len(coverage)==7283
 sets=[set(x['ids']) for x in active]
 assert len(sets)==3 and set(ids) in sets
 for j,s in enumerate(sets):
  assert len(s)==50 and not s.intersection(map(int,coverage)) and not s.intersection(reserve['protected_ids'])
  for t in sets[j+1:]:assert not s&t
 literals=load(P/'literal-records.json');ds=load(P/'dispositions.json')
 assert len(ds)==len(literals)==50 and {x['mathdb_id'] for x in ds}==set(ids)
 assert len(load(P/'proposals.json'))<=3
 lr={x['record']['mathdb_id']:x for x in literals};dr={x['mathdb_id']:x for x in ds}
 # Access exact original line locators; only assigned lines are decoded as scientific records.
 wanted={}
 for x in literals:wanted.setdefault(x['chunk'],{})[x['line']]=x
 for path,locators in wanted.items():
  for line_no,line in enumerate(pathlib.Path(path).open(),1):
   if line_no in locators:assert json.loads(line)==locators[line_no]['record']
 for ident,x in lr.items():
  r=x['record'];d=dr[ident]
  assert d['statement']==r['statement'] and d['canonical_record_sha256']==canonical(r)
  assert d['statement_utf8_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
  assert (d['corpus_chunk'],d['corpus_line'])==(x['chunk'],x['line'])
  assert d['independent_completeness'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  assert all(d[k] for k in ['completeness_reason','quantifiers','technical_assessment'])
  assert d['accepted_credit']==0 and not d['novelty_cleared']
 check(P/'literal-records.json',load(P/'literal-binding.json'))
 for e in load(P/'source-provenance.json'):
  if 'path' in e:check(P/e['path'],e)
 for name,e in load(P/'source-derivative-bindings.json').items():check(P/name,e)
 e=load(P/'render-binding.json');check(P/e['file'],e)
 if '--self-test' in sys.argv:
  for kind in ['hash','size','extra']:
   result=subprocess.run([sys.executable,'-B',__file__,'--negative',kind],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
   assert result.returncode!=0,'negative accepted: '+kind
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'baseline':7283,'original_chunks':20,'frozen_inputs':8,'original_copy_pairs':len(pairs),'reservation_disjointness':True,'negative_tests':['hash','size','extra'] if '--self-test' in sys.argv else [],'scientific_or_novelty_acceptance':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
