import pathlib,json,hashlib,shutil
L=pathlib.Path(__file__).resolve().parent.parent; W=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-circulant-13-prior-adjudication-r481'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def sig(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,r):
 s=sig(p);assert s['sha256']==r['sha256'] and s['size']==r.get('size',r.get('bytes')),str(p);return s
refs=[]
def bind(p,role):
 refs.append({'path':str(p),**sig(p),'role':role})
m=json.loads((I/'manifest.json').read_text());expected={r['path'] for r in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'};assert expected==actual,(expected^actual)
for r in m['files']:check(I/r['path'],r);bind(I/r['path'],'intake exact payload')
bind(I/'manifest.json','intake manifest')
for r in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:check(pathlib.Path(r[k]),r);bind(pathlib.Path(r[k]),'direct '+k)
cm=json.loads((C/'manifest.json').read_text());chunks=[r for r in cm['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for r in chunks+cm['frozen_inputs']:check(C/r['path'],r);bind(C/r['path'],'corpus chunk in place' if r in chunks else 'inventory frozen input')
bind(C/'manifest.json','corpus manifest')
for d,fs in [(I.name,['DECISION.md','adjudications.json','coverage-delta.json','queue-r484.json','reserved-ids-r484.json','reserved-ids.json']),('root-mathdb-accepted-exclusions-r304',['accepted-exclusions.json','historical-dispositions.json']),('root-mathdb-cayley-review-intake-r363',['DECISION.md','disposition.json']),('root-mathdb-breadth-intake-r479',['reserved-ids.json'])]:
 for f in fs:
  p=L/d/f;bind(p,'frozen before reading');out=W/'frozen'/d/f;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,out);refs[-1]['copy']=str(out)
(W/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n');(W/'freeze-receipt.json').write_text(json.dumps({'intake_exact_manifest':'PASS','direct_bindings':'PASS','corpus_chunks':20,'frozen_inputs':8,'before_scientific_read':True},indent=2)+'\n')
print('PASS',len(refs),'flat references; 20 chunks; 8 frozen inputs')
