import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1]
for name in ['openai-preprints','omega-D5','omega-Problems']:
 d=json.loads((L/'downloads'/name/'body').read_text())
 print(name,'entries',len(d['tree']),'truncated',d.get('truncated'))
 assert not d.get('truncated')
 for r in d['tree']:
  if re.search(r'toroid|369421|2507.16469|word.?represent|Kitaev|Pyatkin|Alshammari',r['path'],re.I): print(r['path'])
