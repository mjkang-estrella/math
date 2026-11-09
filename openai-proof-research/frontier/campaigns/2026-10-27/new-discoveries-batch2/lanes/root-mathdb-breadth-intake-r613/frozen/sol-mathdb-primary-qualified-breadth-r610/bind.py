import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r609'
def digest(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def read(p):return json.loads(p.read_text())
# Bind before content: direct intake files, including receipt and manifest.
refs=[digest(p) for p in sorted(I.iterdir()) if p.is_file()]
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
m=read(I/'manifest.json'); expected={x['path'] for x in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert expected==actual
for x in m['files']:
 p=I/x['path'];a=digest(p);assert a['sha256']==x['sha256'] and a['size']==x['size'];refs.append(a)
for x in read(I/'bindings.json'):
 for key in ('original','copy'):
  p=pathlib.Path(x[key]);a=digest(p);assert a['sha256']==x['sha256'] and a['size']==x.get('bytes',x.get('size'));refs.append(a)
(D/'flat-bindings.json').write_text(json.dumps(list({x['path']:x for x in refs}.values()),indent=2)+'\n')
print('Intake exact payload and all original/copy pairs PASS')
# Only structure of inventory is emitted; scientific content remains unread.
p=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json';print(p);print(p.read_text()[:6500])
C=L/'pi-mathdb-full-corpus-inventory-r301';cm=read(C/'manifest.json');chunks=[x for x in cm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for x in chunks+cm['frozen_inputs']:
 p=C/x['path'];a=digest(p);assert a['sha256']==x['sha256'] and a['size']==x['bytes'];refs.append(a)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']+list((L/'root-mathdb-accepted-exclusions-r304').glob('*.json'))+list(L.glob('*r363/DECISION.md')):
 refs.append(digest(p))
(D/'flat-bindings.json').write_text(json.dumps(list({x['path']:x for x in refs}.values()),indent=2)+'\n')
print('All 20 chunks + 8 frozen inputs bound and verified')
for n in ['queue-r610.json','reserved-ids-r610.json','active-breadth-reservations.json','adjudications.json','hypothesis-queue.json','verification-receipt.json']:
 print('\n'+n+'\n'+(I/n).read_text())
