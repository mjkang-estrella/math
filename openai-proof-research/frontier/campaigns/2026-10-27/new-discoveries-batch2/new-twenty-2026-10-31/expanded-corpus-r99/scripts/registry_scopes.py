from fetch import fetch
import pathlib,json,re
L=pathlib.Path.cwd()
for repo,scopes in [('openai/math',['preprints']),('the-omega-institute/trureturing',['D5','Problems'])]:
 slug=repo.replace('/','-');j=json.load(open('sources/'+slug+'-HEAD.json'));sha=j['commit']['tree']['sha'];fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,slug+'-root.json');root=json.load(open('sources/'+slug+'-root.json'))
 for name in scopes:
  x=next((x for x in root['tree']if x['path']==name),None)
  if x:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+x['sha']+'?recursive=1',slug+'-'+name+'.json')
for p in pathlib.Path('sources').glob('*.json'):
 if not any(x in p.name for x in ['-D5','-Problems','-preprints']):continue
 j=json.loads(p.read_text());print(p.name,'truncated',j.get('truncated'))
 for x in j.get('tree',[]):
  if re.search(r'pagerank|dope|jet.?graph|wachs|peak.?polynomial|entropoid|deeply.?critical|350434|350451|356988|354691|381793|351090',x['path'],re.I):print(x['path'])
