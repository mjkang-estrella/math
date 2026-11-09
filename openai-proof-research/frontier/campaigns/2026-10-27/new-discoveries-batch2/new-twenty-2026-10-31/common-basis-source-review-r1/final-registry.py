from pathlib import Path
import json,runpy
L=Path(__file__).resolve().parent;fetch=runpy.run_path(str(L/'fetch.py'))['fetch'];h=json.loads((L/'receipts/openai-head.json').read_text())['sha'];root=json.loads((L/'receipts/openai-oai-root.json').read_text())
for e in root['tree']:
 if e['path'] in ['Combinatorics','Algorithms','Optimization']:
  d=json.loads(fetch('openai-OAI-'+e['path']+'.json','https://api.github.com/repos/openai/math/git/trees/'+e['sha']+'?recursive=1'));print(e['path'],'truncated',d.get('truncated'),flush=True)
  for x in d.get('tree',[]):
   p=x['path']
   if x['type']=='blob' and any(w in p.lower() for w in ['matroid','commonbases','common_bases','complementarybases']) and p.endswith('.lean'):
    fetch('openai-lean--'+e['path']+'__'+p.replace('/','__'),'https://raw.githubusercontent.com/openai/math/'+h+'/lean/OAI/'+e['path']+'/'+p)
fetch('openai-CommonBasesFPRAS.lean','https://raw.githubusercontent.com/openai/math/'+h+'/lean/ComparatorChallenges/CommonBasesFPRAS.lean')
