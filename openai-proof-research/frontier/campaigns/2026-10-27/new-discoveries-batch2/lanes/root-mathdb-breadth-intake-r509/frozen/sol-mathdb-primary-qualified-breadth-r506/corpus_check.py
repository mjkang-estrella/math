from pathlib import Path
exec(Path(__file__).with_name('intake_check.py').read_text().split('binds=')[0])
r=load(L/'pi-mathdb-full-corpus-inventory-r301/manifest.json'); print('frozen schema',r.get('frozen_inputs'))
a=[e for e in r['files'] if e['path'].startswith('corpus/')];assert len(a)==20
for e in a:
 p=L/'pi-mathdb-full-corpus-inventory-r301'/e['path'];v=h(p);assert v['size']==e['bytes'] and v['sha256']==e['sha256']
print('20 chunks passed')
for name in ['active-breadth-reservations.json','reserved-ids-r506.json','coverage-summary.json']:
 print(name,load(I/name))
c=load(I/'coverage-delta.json');print('coverage schema',str(c)[:1600]);print('r301 keys',r.keys())
