#!/usr/bin/env python3
"""Read-only independent verifier. Run through verify.sh / fixed helper guard."""
import pathlib,json,hashlib,sys,collections
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r641';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')), 'size mismatch: '+str(p);assert h(b)==e['sha256'],'hash mismatch: '+str(p)
def exact(root,m,negative=None):
 assert set(m['excluded_exact_paths'])==({'manifest.json','final-verification-receipt.json'} if root==P else {'manifest.json','verification-receipt.json'})
 names={e['path'] for e in m['files']};assert len(names)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('__virtual_extra__')
 assert actual==names,'extra/missing payload'
 for i,e0 in enumerate(m['files']):
  e=dict(e0)
  if i==0 and negative=='size':e['size']+=1
  if i==0 and negative=='hash':e['sha256']='0'*64
  check(root/e['path'],e)
def validate(negative=None):
 exact(P,j(P/'manifest.json'),negative)
 # These bindings predate corpus reading and include immutable manifest/receipt metadata.
 for n in ['initial-bindings.json','flat-bindings.json','download-bindings.json']:
  for e in j(P/n):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 # Verify original inventory against the intake's independently bound original/copy pair.
 matches=[e for e in pairs if e['original']==str(C/'manifest.json')];assert len(matches)==1
 check(C/'manifest.json',matches[0]);check(pathlib.Path(matches[0]['copy']),matches[0])
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==6933
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==len(r['ids'])==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids']);assert r['active_hypothesis_ids']==[]
 assert next(r for r in active if 'r628' in r['lane'])['status']=='rate_limit_held_not_reconciled'
 res=j(I/'reserved-ids-r642.json');ids=set(res['ids']);assert res['coverage_baseline']==6933 and res['lane']==P.name
 assert next(r for r in active if r['lane']==P.name)['ids']==res['ids']
 assert ids=={r['mathdb_id'] for r in j(I/'queue-r642.json')}
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 assert len(j(P/'proposals.json'))<=3 and j(P/'proposals.json')==[]
 found={}
 for e in chunks:
  p=C/e['path']
  with p.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in ids:
     assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 literal={d['record']['mathdb_id']:d for d in j(P/'literal-records.json')};assert set(literal)==ids
 rows={}
 for s in (P/'reviews.tsv').read_text().splitlines():
  i,c,q,t=s.split('\t');assert int(i) not in rows;rows[int(i)]=(c,q,t)
 assert set(rows)==ids
 cats=collections.Counter()
 for d in ds:
  p,n,r=found[d['mathdb_id']];i=d['mathdb_id'];cat,q,t=rows[i]
  assert d['corpus_chunk']==str(p.resolve()) and d['corpus_line']==n
  assert literal[i]=={'corpus_chunk':str(p.resolve()),'corpus_line':n,'record':r}
  assert d['statement_utf8']==r['statement'] and d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['quantifiers']==q and d['technical_disposition']==t and d['independent_scope_classification']==cat
  assert cat in {'complete','definition-dependent','scope-ambiguous','incomplete'};cats[cat]+=1
  assert d['accepted_credit']==0 and d['current_registry_cleared'] is False and d['full_dependency_audit'] is False and d['whole_body_review'] is False
  assert d['source_url']==r['source_url'] and d['record_references']==r['references']
  if cat=='incomplete':assert d['disposition']=='HOLD_INCOMPLETE'
 coverage=j(P/'source-coverage.json');assert coverage['independent_scope_categories']==dict(cats)
 assert sum(d['source_evidence']['level']!='literal_record_only' for d in ds)==coverage['selected_question_theorem_or_answer_passage_records']==9
 for e in j(P/'selected-passages.json'):
  s=(P/e['file']).read_text();assert s[e['start_utf8_character']:e['end_utf8_character']]==e['passage']
 assert j(P/'bounded-checks.json')['executed'] is True and all(x['holds'] for x in j(P/'bounded-checks.json')['results'])
 # Receipt, if present, must pin this manifest; it is deliberately not self-hashed.
 receipt=P/'final-verification-receipt.json'
 if receipt.exists():check(P/'manifest.json',j(receipt)['manifest'])
 return {'integrity':'PASS','literal_records':50,'scope_categories':dict(cats),'original_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(pairs),'baseline':6933,'disjoint_reserved_sets':3,'proposals':0,'credit':0,'math_novelty_acceptance':False}
if __name__=='__main__':
 try:print(json.dumps(validate(sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
