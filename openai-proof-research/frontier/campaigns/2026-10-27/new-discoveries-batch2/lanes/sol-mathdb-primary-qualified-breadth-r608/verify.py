"""Independent read-only verifier. Run under the fixed helper_guard.py; optional payload root for negative tests."""
import pathlib,json,hashlib,sys
P=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else pathlib.Path(__file__).resolve().parent
L=pathlib.Path(__file__).resolve().parent.parent
I=L/'root-mathdb-breadth-intake-r605';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(p):
 b=p.read_bytes();return hashlib.sha256(b).hexdigest(),len(b)
def check(p,e):
 h,n=digest(p);assert n==e.get('size',e.get('bytes')),f'size mismatch: {p}'
 assert h==e['sha256'],f'hash mismatch: {p}'
def payload(root,m):
 assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 assert actual==expected,f'extra/missing payload: {actual^expected}'
 for e in m['files']:check(root/e['path'],e)
payload(P,load(P/'manifest.json'))
refs=load(P/'flat-bindings.json');assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(pathlib.Path(e['path']),e)
ref={e['path']:e for e in refs}
assert digest(I/'manifest.json')==('d2910a960ea63a6ff6d9d7f8f241abb2a541c124b94d073b135190d824b37849',17319)
m=load(I/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','verification-receipt.json'}
expected={e['path'] for e in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert expected==actual
for e in m['files']:check(I/e['path'],e);assert str(I/e['path']) in ref
for e in load(I/'bindings.json'):
 a,b=pathlib.Path(e['original']),pathlib.Path(e['copy']);check(a,e);check(b,e);assert a.read_bytes()==b.read_bytes()
rm=load(R/'manifest.json');check(R/'manifest.json',ref[str(R/'manifest.json')]);chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:check(R/e['path'],e);assert str(R/e['path']) in ref
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 assert (R/'frozen/root-mathdb-accepted-exclusions-r304'/n).read_bytes()==(L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()
r=load(I/'reserved-ids-r608.json');q=load(I/'queue-r608.json');c=load(I/'coverage-delta.json');assert len(c)==6133 and r['coverage_baseline']==6133
reserved=set(r['ids']);assert len(reserved)==50==len(q) and reserved=={x['mathdb_id'] for x in q}
sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')];assert len(sets)==3 and reserved in sets
protected=set(r['protected_ids']+[343771,343973,344924,383181])
for j,s in enumerate(sets):
 assert not s&set(map(int,c)) and not s&protected
 for t in sets[:j]:assert not s&t
rows=load(P/'literal-records.json');ds=load(P/'dispositions.json');assert len(rows)==len(ds)==50
assert {x['mathdb_id'] for x in rows}=={x['mathdb_id'] for x in ds}==reserved
assert len({x['mathdb_id'] for x in ds})==50
byid={x['mathdb_id']:x for x in ds};assigned={x['mathdb_id']:x for x in q}
for x in rows:
 p=pathlib.Path(x['chunk']);assert str(p) in {str(R/e['path']) for e in chunks}
 with p.open() as f:
  for j,line in enumerate(f,1):
   if j==x['line']:o=json.loads(line);break
 assert o==x['record'] and o['mathdb_id']==x['mathdb_id']
 canonical=hashlib.sha256(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 d=byid[x['mathdb_id']];assert canonical==x['canonical_record_sha256']==d['canonical_record_sha256']
 assert d['corpus_chunk']==x['chunk'] and d['corpus_line']==x['line']
 assert d['statement_exact_utf8']==o['statement'] and d['statement_utf8_sha256']==hashlib.sha256(o['statement'].encode()).hexdigest()
 assert o['title']==assigned[o['mathdb_id']]['title'] and o['canonical_url']==assigned[o['mathdb_id']]['canonical_url']
 assert d['accepted_credit']==0 and not d['novelty_pass'] and not d['current_registry_clearance'] and d['quantifiers_reviewed'] and d['technical_assessment']
 assert d['complete_mathematical_statement_review']==(d['literal_statement_scope']=='complete')
assert load(P/'proposals.json')==[]
for e in load(P/'source-provenance.json'):
 if 'file' in e:check(P/e['file'],e)
for e in load(P/'derivative-bindings.json'):check(P/e['path'],e)
print(json.dumps({'integrity_pass':True,'math_or_novelty_pass':False,'literal_records':50,'complete_literal_statements':sum(d['complete_mathematical_statement_review'] for d in ds),'definition_dependent_or_incomplete':sum(not d['complete_mathematical_statement_review'] for d in ds),'proposals':0,'corpus_chunks_checked_in_place':20,'frozen_inputs_checked':8,'baseline':6133,'manifest_sha256':digest(P/'manifest.json')[0],'manifest_size':digest(P/'manifest.json')[1]},sort_keys=True))
