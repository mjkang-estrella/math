import pathlib,json,sys,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
x=json.loads((D/'extracted.json').read_text());ids=list(x)
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 tree=json.loads((D/f'sources/{key}-tree.json').read_text());print(key,'truncated',tree.get('truncated'))
 hits=[o for o in tree['tree'] if any(i in o['path'] for i in ids) or re.search('meandr|heterochrom|exponential.?dom|ghost.?number|Saxl|saxl|clique.width',o['path'],re.I)]
 (D/f'outputs/{key}-path-hits.json').write_text(json.dumps(hits,indent=2))
 for o in hits:print(o['path'])
 head=json.loads((D/f'sources/{key}-head.json').read_text())['sha']
 for j,o in enumerate(hits):
  if o['type']=='blob' and o['path'].endswith(('.md','.tex','.lean','.json')) and len(o['path'])<200 and j<40:get(f'{key}-hit-{j:02d}'+pathlib.Path(o['path']).suffix,f'https://raw.githubusercontent.com/{repo}/{head}/'+o['path'])
