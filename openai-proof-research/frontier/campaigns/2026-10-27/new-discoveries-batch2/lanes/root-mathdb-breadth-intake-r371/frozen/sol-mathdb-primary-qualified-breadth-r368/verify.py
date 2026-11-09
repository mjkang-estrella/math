from pathlib import Path
import json,hashlib,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,e):assert p.is_file() and p.stat().st_size==e.get('size',e.get('bytes')) and sha(p)==e['sha256'],str(p)
def load(p):return json.loads(p.read_text())
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if len(sys.argv)>1 and sys.argv[1]=='manifest':
 (R/'manifest.json').write_text(json.dumps({'files':[{'path':p,'size':(R/p).stat().st_size,'sha256':sha(R/p)} for p in sorted(payload())]},indent=2)+'\n')
 print('MANIFEST BUILT');sys.exit(0)
for e in load(R/'bindings.json')['files']:check(Path(e['path']),e)
manifest_counts={}
for name in ['root-mathdb-breadth-intake-r367','pi-mathdb-full-corpus-inventory-r301']:
 base=L/name;es=load(base/'manifest.json')['files']
 for e in es:check(base/e['path'],e)
 manifest_counts[name]=len(es)
corpus=[e for e in load(L/'pi-mathdb-full-corpus-inventory-r301/manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(corpus)==20
A=[str(x) for x in load(L/'root-mathdb-breadth-intake-r367/reserved-ids.json')['ids']]
B=[str(x) for x in load(L/'root-mathdb-gram-intake-r359/reserved-ids.json')['ids']]
C=[str(x) for x in load(L/'root-mathdb-breadth-intake-r365/reserved-ids.json')['ids']]
assert all(len(x)==len(set(x))==50 for x in [A,B,C]);assert not (set(A)&set(B) or set(A)&set(C) or set(B)&set(C))
assert '364119' not in A
assert set(A)=={str(x['mathdb_id']) for x in load(L/'root-mathdb-breadth-intake-r367/queue.json')}
old=load(L/'root-mathdb-breadth-intake-r367/coverage-delta.json');assert len(old)==683 and not set(A)&set(old)
found={}
for e in corpus:
 p=L/'pi-mathdb-full-corpus-inventory-r301'/e['path'];check(p,e)
 for lineno,line in enumerate(p.open(),1):
  x=json.loads(line);n=str(x['mathdb_id'])
  if n in A:
   assert n not in found;found[n]=(x,p,lineno)
assert set(found)==set(A)
rows=load(R/'dispositions.json');assert len(rows)==50 and len({str(x['mathdb_id']) for x in rows})==50
assert {str(x['mathdb_id']) for x in rows}==set(A)
for x in rows:
 original,p,lineno=found[str(x['mathdb_id'])]
 assert x['literal_statement']==original['statement'] and x['statement_sha256']==hashlib.sha256(x['literal_statement'].encode()).hexdigest()
 assert x['record_ref']['path']==str(p.resolve()) and x['record_ref']['line']==lineno
 assert x['record_ref']['record_canonical_json_sha256']==hashlib.sha256(json.dumps(original,sort_keys=True,ensure_ascii=False).encode()).hexdigest()
 assert x['reason'] and x['credit']==0 and x['record_statement_review'] and not x['complete_dependency_review']
assert sum(x['primary_body_review'] for x in rows)==10
assert sum(x['successor_body_review'] for x in rows)==2
assert sum(x['proof_section_review'] for x in rows)==2
assert sum(x['concluding_proof_section_review'] for x in rows)==0
assert load(R/'proposals.json')==[]
assert load(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json')['accepted_family_count']==39
assert load(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['credit']==0
for e in load(R/'sources.json'):
 if e.get('accepted_content'):check(R/e['path'],e)
entries=load(R/'manifest.json')['files'];assert len(entries)==len({e['path'] for e in entries}) and payload()=={e['path'] for e in entries}
for e in entries:check(R/e['path'],e)
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'separate_final_run':True,'original_bindings':len(load(R/'bindings.json')['files']),'manifests':manifest_counts,'corpus_chunks':20,'exact_reserved':50,'other_disjoint_reserved':100,'baseline_coverage':683,'record_statement_reviews':50,'primary_body_reviews':10,'successor_body_reviews':2,'partial_proof_section_reviews':2,'complete_dependency_reviews':0,'proposals':0,'credit':0,'manifest_files':len(entries),'manifest_sha256':sha(R/'manifest.json'),'counts_unchanged':{'additional':9,'total':39,'next':40}}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
