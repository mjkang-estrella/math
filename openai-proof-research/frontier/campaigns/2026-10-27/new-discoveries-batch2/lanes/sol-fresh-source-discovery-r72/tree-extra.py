import json,pathlib,re
base=pathlib.Path('../sol-fresh-source-discovery-r58/sources')
for p in base.glob('*tree.json'):
 d=json.loads(p.read_text())
 if isinstance(d,dict):
  print(p.name,[(x['path']) for x in d.get('tree',[]) if re.search('Khin|Khint|Moment|ConvexOrder|Rademach|SymmetricSum|Tcheby',x['path'],re.I)][:100])
