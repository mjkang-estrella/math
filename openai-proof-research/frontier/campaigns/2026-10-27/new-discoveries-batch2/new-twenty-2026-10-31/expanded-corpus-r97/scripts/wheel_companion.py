from fetch import get,D
import json
repo='https://api.github.com/repos/Shivaramkratos/Ultimate_Independence_ratio_Python_Gurobi_code'
print(get(('wheel-code-head.json',repo+'/commits/HEAD')))
p=D/'sources/wheel-code-head.json'
if p.exists():
 h=json.loads(p.read_text());print(get(('wheel-code-tree.json',repo+'/git/trees/'+h['commit']['tree']['sha']+'?recursive=1')))
 t=D/'sources/wheel-code-tree.json'
 if t.exists():
  for e in json.loads(t.read_text()).get('tree',[]):
   path=e['path']
   if e['type']=='blob' and any(x in path.lower() for x in ['readme','fraction','profile','chromat']):
    print(get(('wheel-code-'+path.replace('/','_'),'https://raw.githubusercontent.com/Shivaramkratos/Ultimate_Independence_ratio_Python_Gurobi_code/'+h['sha']+'/'+path)))
