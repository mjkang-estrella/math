import sys,pathlib,json,re
exec((pathlib.Path(__file__).parent/'fetch.py').read_text())
if mode=='follow':
 sha=json.loads((D/'sources/lean-pool-head.json').read_text())['sha']
 tree=json.loads((D/'sources/lean-pool-tree.json').read_text())
 for x in tree['tree']:
  if x['type']=='blob' and re.search(r'CommonNeighbourConjecture/(Main|Result|README|Saxl/Generalized)|CommonNeighbourConjecture\.lean',x['path']):get(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+x['path'],'pool-'+x['path'].replace('/','_'))
 for a in ['2610.06445','2602.21895','2504.21805']:
  get('https://arxiv.org/abs/'+a,a+'-abs.html');get('https://arxiv.org/html/'+a,a+'-body.html')
 for repo in ['the-omega-institute/trureturing','openai/math']:
  key=repo.split('/')[-1];sha=json.loads((D/'sources'/(key+'-head.json')).read_text())['sha']
  b=get(f'https://api.github.com/repos/{repo}/git/trees/{sha}',key+'-root.json')
  if b:
   for x in json.loads(b)['tree']:
    if x['path'] in ['D5','Problems','preprints']:
     get(f'https://api.github.com/repos/{repo}/git/trees/'+x['sha']+'?recursive=1',key+'-'+x['path']+'-tree.json')
