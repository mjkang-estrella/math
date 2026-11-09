from pathlib import Path
import hashlib,json,datetime,sys
R=Path(__file__).resolve().parent;L=R.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 size=e.get('size',e.get('bytes'))
 assert (size is None or p.stat().st_size==size) and sha(p)==e['sha256'],str(p)
def manifest(d,exact=False):
 m=json.loads((d/'manifest.json').read_text());m=m.get('files',m) if isinstance(m,dict) else m
 if isinstance(m,dict):m=[dict(v,path=k) for k,v in m.items()]
 for e in m:check(d/e['path'],e)
 if exact:assert {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in m}
 return m
for e in json.loads((R/'bindings.json').read_text())['files']:check(Path(e['path']),e)
a=L/'root-mathdb-cayley-review-intake-r363';manifest(a,True)
for e in json.loads((a/'bindings.json').read_text()):check(Path(e['original']),e)
b=L/'root-mathdb-accepted-exclusions-r304';manifest(b)
assert json.loads((b/'accepted-exclusions.json').read_text())['accepted_family_count']==39
assert (b/'historical-dispositions.json').stat().st_size>0
assert json.loads((a/'disposition.json').read_text())['mathdb_id']==364119
assert json.loads((a/'disposition.json').read_text())['credit']==0
m=json.loads((L/'pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text())
chunks=[e for e in m['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(L/'pi-mathdb-full-corpus-inventory-r301'/e['path'],e)
ids=json.loads((a/'reserved-ids.json').read_text())['ids'];q=json.loads((a/'queue.json').read_text());assert set(ids)=={x['mathdb_id'] for x in q}
cov=json.loads((a/'coverage-delta.json').read_text());assert len(cov)==583
sets=[set(json.loads((L/n/'reserved-ids.json').read_text())['ids']) for n in ['root-mathdb-breadth-intake-r361','root-mathdb-gram-intake-r359']]
assert len(ids)==len(set(ids))==50 and all(len(s)==50 for s in sets)
assert not sets[0]&sets[1] and not set(ids)&(sets[0]|sets[1]) and all(not s&set(map(int,cov)) for s in sets+[set(ids)])
assert not {364119,404067}&set(ids)
ds=json.loads((R/'dispositions.json').read_text());assert len(ds)==50 and {x['mathdb_id'] for x in ds}==set(ids)
refs=json.loads((R/'record-refs.json').read_text());wanted={}
for r in refs:wanted.setdefault(r['path'],{})[r['line']]=r['id']
actual={}
for p,lines in wanted.items():
 for i,line in enumerate(Path(p).open(),1):
  if i in lines:
   x=json.loads(line);assert x['mathdb_id']==lines[i];actual[x['mathdb_id']]=x
for d in ds:assert d['literal_statement']==actual[d['mathdb_id']]['statement'] and d['credit']==0
assert sum(d['primary_statement_review'] for d in ds)==5 and sum(d['complete_proof_dependency_coverage'] for d in ds)==1
assert json.loads((R/'proposals.json').read_text())==[]
for e in json.loads((R/'sources.json').read_text()):check(R/e['file'],e)
assert json.loads((R/'exact-check.json').read_text())['unit_cases']==180
manifest(R,True)
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'separate_final_run':True,'original_corpus_chunks':20,'coverage_baseline':583,'reserved_sets':[50,50,50],'literal_statements':50,'primary_statements':5,'proposals':0,'credit':0,'counts':'9additional/39total/next40 unchanged','manifest_sha256':sha(R/'manifest.json')}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
