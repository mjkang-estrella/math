import importlib.util,json,pathlib
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
print({m:bool(importlib.util.find_spec(m)) for m in ['numpy','scipy','sympy','networkx','shapely','z3']})
for f in D.glob('sources/github-search-*.json'):
 j=json.loads(f.read_text());print(f.name,j.get('total_count'),[(x['full_name'],x.get('description')) for x in j.get('items',[])][:5])
