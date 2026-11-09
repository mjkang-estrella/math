import sys,json,subprocess
from fetch import get,D
for repo,key in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 h=json.loads((D/f'sources/{key}-head.json').read_text())['sha']
 name=key+'-root.json'; print(get((name,f'https://api.github.com/repos/{repo}/git/trees/{h}')),flush=True)
 p=D/'sources'/name
 if not p.exists():continue
 root=json.loads(p.read_text())
 for x in root.get('tree',[]):
  if x['path'] in ['D5','Problems','preprints']:
   print(get((key+'-'+x['path']+'-tree.json',f"https://api.github.com/repos/{repo}/git/trees/{x['sha']}?recursive=1")),flush=True)
