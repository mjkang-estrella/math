import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent; L=P.parent; I=L/'root-mathdb-breadth-intake-r691'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
out=[entry(I/'manifest.json'),entry(I/'verification-receipt.json')]
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:out.append(check(I/e['path'],e))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:out.append(check(pathlib.Path(e[k]),e))
cm=j(C/'manifest.json');check(C/'manifest.json',next(e for e in j(I/'bindings.json') if e['original']==str(C/'manifest.json')))
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:out.append(check(C/e['path'],e))
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'pi-mathdb-full-corpus-inventory-r304/accepted-exclusions.json',L/'pi-mathdb-full-corpus-inventory-r304/historical-dispositions.json']:
 if p.exists():out.append(entry(p))
(P/'initial-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS intake exact payload; all direct pairs; 20 chunks; 8 frozen inputs. Bound',len(out),'references')
print('inventory frozen',cm['frozen_inputs'])
for n in ['queue-r692.json','reserved-ids-r692.json','active-breadth-reservations.json']:
 x=j(I/n);print(n, type(x).__name__,str(x)[:2500])
print('r304 paths',list(L.glob('*r304*')),'r363',list(L.glob('*r363*')))
