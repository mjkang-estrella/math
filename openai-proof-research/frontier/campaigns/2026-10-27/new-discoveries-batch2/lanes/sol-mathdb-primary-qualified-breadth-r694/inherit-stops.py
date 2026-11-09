import pathlib,json,hashlib
P=pathlib.Path(__file__).parent;L=P.parent
j=lambda p:json.loads(p.read_text())
b=j(P/'flat-bindings.json');paths=[]
for n in [578,642,684]:
 for name in ['failures.json','failures.md','source-provenance.json','fetch-provenance.json']:
  p=L/f'sol-mathdb-primary-qualified-breadth-r{n}'/name
  if p.exists():
   x=p.read_bytes();b.append({'path':str(p.resolve()),'size':len(x),'sha256':hashlib.sha256(x).hexdigest()});paths.append(p)
(P/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
# Content read only after above bindings saved. Keep exact failures, do not fetch.
f=j(P/'failures.json');f['exact_inherited_failure_evidence']=[]
for p in paths:
 if p.name in ['failures.json','failures.md']:
  o=j(p) if p.suffix=='.json' else p.read_text();f['exact_inherited_failure_evidence'].append({'path':str(p.resolve()),'failure_payload':o});print(p.parent.name,json.dumps(o))
(P/'failures.json').write_text(json.dumps(f,ensure_ascii=False,indent=2)+'\n')
c=j(P/'source-coverage.json');c['primary']['319684']+='; additionally definitions20/Proposition21 lines924-965 read. Nonrepresentable constants cannot be composites and none can be a universal unit for positive-square addition.';(P/'source-coverage.json').write_text(json.dumps(c,ensure_ascii=False,indent=2)+'\n')
