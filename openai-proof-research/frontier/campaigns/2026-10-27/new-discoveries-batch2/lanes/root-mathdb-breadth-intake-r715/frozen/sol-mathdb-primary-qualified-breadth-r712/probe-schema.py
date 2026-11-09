import json,pathlib
L=pathlib.Path(__file__).resolve().parent.parent
for p in ['pi-mathdb-full-corpus-inventory-r301/manifest.json','root-mathdb-breadth-intake-r711/active-breadth-reservations.json','root-mathdb-breadth-intake-r711/coverage-delta.json']:
 d=json.loads((L/p).read_text());print(p, list(d) if isinstance(d,dict) else ['list',len(d)])
 if 'manifest' in p:print('frozen_inputs',d.get('frozen_inputs'));print('lastfiles',d['files'][-3:])
 elif 'reservations' in p:print(json.dumps(d)[:9000])
 else:print(json.dumps(d)[:1500])
