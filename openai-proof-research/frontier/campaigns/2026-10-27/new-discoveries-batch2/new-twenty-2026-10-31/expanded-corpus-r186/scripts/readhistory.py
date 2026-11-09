import pathlib,json
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186'); h=json.loads((L/'outputs/history.json').read_text())
for i,x in h.items():
 for f in x['hits']:
  obj=json.loads(pathlib.Path(f).read_text())
  if isinstance(obj,dict) and i in obj:print(i,json.dumps(obj[i])[:5000])
  else:
   for line in pathlib.Path(f).read_text().splitlines():
    if i in line: print(i,line[:1000])
