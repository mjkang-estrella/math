import pathlib,json,re,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
tree=json.loads((L/'sources/omega-tree.json').read_text())
print('recursive_root_truncated',tree.get('truncated'))
print('relevant_paths:')
for x in tree['tree']:
 if re.search('word.?repr|toroid|grid|cylind|majority|riesz|liking|sturmian|cycle.?system|star.?forest|monotone.?path',x['path'],re.I):print(x['path'],x['sha'])
print('root directories',[(x['path'],x['sha']) for x in tree['tree'] if '/' not in x['path'] and x['type']=='tree'])
