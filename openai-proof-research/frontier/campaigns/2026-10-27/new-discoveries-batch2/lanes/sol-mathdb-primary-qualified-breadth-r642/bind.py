import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r641';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return {'path':str(p.resolve()),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=binding(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
a=j(P/'initial-bindings.json')
for e in a:check(pathlib.Path(e['path']),e)
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e);a.append(binding(I/e['path']))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);a.append(binding(pathlib.Path(e[k])))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);a.append(binding(C/e['path']))
# Bind relevant flat references without expanding historical trees.
for p in [L/'sol-mathdb-primary-qualified-breadth-r638/flat-bindings.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 a.append(binding(p))
for e in j(L/'sol-mathdb-primary-qualified-breadth-r638/flat-bindings.json'):
 p=pathlib.Path(e['path']);check(p,e);a.append(binding(p))
a=list({e['path']:e for e in a}.values());(P/'flat-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==6933
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert len(seen)==150
ids=set(j(I/'reserved-ids-r642.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r642.json')}
found=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append({'corpus_chunk':str(p.resolve()),'corpus_line':n,'record':r})
assert len(found)==50
(P/'literal-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
(P/'binding-check.json').write_text(json.dumps({'intake_exact':True,'direct_pairs':len(j(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'coverage_baseline':6933,'disjoint_reserved_sets':3,'flat_references':len(a)},indent=2)+'\n')
print('binding PASS',len(a));print('reference paths',*[e['path'] for e in a if any(s in e['path'] for s in ['r304','r363'])],sep='\n')
for d in found:
 r=d['record'];print('\nID',r['mathdb_id'],r.keys());print(r['statement']);print('sources',r.get('sources',r.get('references')))
