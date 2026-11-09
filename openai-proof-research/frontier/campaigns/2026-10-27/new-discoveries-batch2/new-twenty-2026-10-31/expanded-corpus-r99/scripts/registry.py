from fetch import fetch
import json,pathlib,re
L=pathlib.Path.cwd()
for repo in ['openai/math','the-omega-institute/trureturing']:
 j=json.loads((L/'sources'/(repo.replace('/','-')+'-HEAD.json')).read_text()); print(repo,j['sha'])
 fetch('https://api.github.com/repos/'+repo+'/git/trees/'+j['commit']['tree']['sha']+'?recursive=1',repo.replace('/','-')+'-tree.json')
for p in (L/'sources').glob('*-tree.json'):
 j=json.loads(p.read_text()); matches=[x for x in j.get('tree',[]) if re.search('pagerank|dope|wachs|jet.graph|peak.polynomial|partition.function|entropoid|deeply.critical|gap.free|rainbow.match|snake|hook.length',x['path'],re.I)]
 print(p.name,'truncated',j.get('truncated'),json.dumps(matches))
