import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in [D/'outputs/submod-dual-min.json',D/'outputs/registry-screen.json',D/'outputs/kreweras-search.json']:
 if not p.exists():continue
 z=json.loads(p.read_text())
 if 'dual' in p.name:print(p.name,z['exact_balance'],len(z['support']),[(x['kind'],x.get('point'),x['weight']) for x in z['support'] if x['kind']!='submodular'])
 elif 'registry' in p.name:print('queries',z['github_query_results']);print('341850 paths',{k:v.get('keyword_hits',{}).get('341850') for k,v in z.items() if k.endswith('-scope')})
 else:print(z)
