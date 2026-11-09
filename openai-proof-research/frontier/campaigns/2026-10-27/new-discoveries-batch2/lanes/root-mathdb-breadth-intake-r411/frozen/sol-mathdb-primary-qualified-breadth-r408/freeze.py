import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; I=B/'root-mathdb-breadth-intake-r407'; C=B/'pi-mathdb-full-corpus-inventory-r301'
def ref(p):
 b=p.read_bytes(); return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 r=ref(p);assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),str(p);return r
refs={}
paths=[I/x for x in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json','verify.py']]+[C/'manifest.json',B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',B/'root-mathdb-cayley-review-intake-r363/disposition.json',B.parent/'ledger.json',B.parent/'prior-campaign-context.json']
for p in paths: refs[str(p)]=ref(p)
for e in json.loads((I/'manifest.json').read_text())['files']:
 p=I/e['path'];refs[str(p)]=check(p,e)
for e in json.loads((I/'bindings.json').read_text()):
 p=pathlib.Path(e['original']);refs[str(p)]=check(p,e)
chunks=[]
for e in json.loads((C/'manifest.json').read_text())['files']:
 if e['path'].startswith('corpus/mathdb-normalized-chunk-'):
  r=check(C/e['path'],e); refs[r['path']]=r;chunks.append(r['path'])
assert len(chunks)==20
(L/'bindings.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'style':'flat references only; no corpus/history copies','references':list(refs.values()),'corpus_chunks':chunks},indent=2)+'\n')
print('FROZEN',len(refs),'refs; twenty chunks verified; upstream manifest verified read-only')
