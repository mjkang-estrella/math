import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in ['eigen-2-6.json','eigen-7-7.json','groups.json','om.json','bip.json']:
 f=D/'outputs'/p
 if not f.exists():continue
 a=json.loads(f.read_text());print(p,len(a))
 if p.startswith('eigen'):print([(x['k'],[(c['l'],c['larger_values'],c['nonnegative_above']) for c in x['checks']]) for x in a])
 if p.startswith('om'):print([(x['n'],x['maximum'],x['maxima_count'],x['nontrivial_components'],len(x['bad'])) for x in a])
 if p.startswith('bip'):print(a)
