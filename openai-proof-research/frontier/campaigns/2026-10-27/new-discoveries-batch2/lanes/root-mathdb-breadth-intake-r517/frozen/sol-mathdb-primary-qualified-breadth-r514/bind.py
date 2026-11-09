import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r513';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
assert entry(I/'manifest.json')['sha256']=='5b44418b7b4406dd84f4de4154e26ca17cace1e05b99cc1985e193e65fb8a2b3'
paths={I/'manifest.json',I/'verification-receipt.json'}
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e);paths.add(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);paths.add(pathlib.Path(e[k]))
cm=j(C/'manifest.json');ce=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(ce)==20 and len(cm['frozen_inputs'])==8
for e in ce+cm['frozen_inputs']:check(C/e['path'],e);paths.add(C/e['path'])
# Bind required context without reading its scientific/admin contents.
for root,pat in [(L,'*r304*'),(L,'*r363*')]:
 for d in root.glob(pat):
  for p in d.iterdir():
   if p.is_file() and (p.suffix in ['.json','.md']):paths.add(p)
B=L.parent;R=B.parents[2]
for p in [B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']:
 if p.exists():paths.add(p)
write('flat-bindings.json',[entry(p) for p in sorted(paths)])
cov=j(I/'coverage-delta.json');assert len(cov)==3883
res=j(I/'reserved-ids.json');q=j(I/'queue.json');ids=set(res['ids']);assert res['lane']==P.name and len(q)==len(ids)==50 and ids=={r['mathdb_id'] for r in q}
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not set(map(str,s))&set(cov) and not s&set(r['protected_ids']);seen|=s
found=[]
for e in ce:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append(dict(mathdb_id=r['mathdb_id'],corpus_chunk=str(p),corpus_line=n,record=r,statement=r['statement'],statement_utf8_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(found)==50 and {r['mathdb_id'] for r in found}==ids
write('assigned-records.json',found)
write('initial-verification.json',dict(intake_exact=True,direct_pairs=True,chunks=20,frozen_inputs=8,baseline=3883,reservation_sets=3,reserved_total=150,disjoint=True,assigned=50))
print(json.dumps(j(P/'initial-verification.json')))
print('CONTEXT',*[str(p) for p in sorted(paths) if 'r304' in str(p) or 'r363' in str(p)],sep='\n')
