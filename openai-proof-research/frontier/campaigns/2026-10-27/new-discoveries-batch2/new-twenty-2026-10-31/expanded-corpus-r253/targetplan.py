from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent;D=L/'http';jobs=[]
for name,repo,roots in [('openai','openai/math',['preprints','lean/OAI/Combinatorics','lean/ComparatorChallenges']),('omega','the-omega-institute/trureturing',['Truth','Blueprint','D5','problems']),('pool','Vilin97/lean-pool',[])]:
 t=json.loads((D/(name+'-tree.json')).read_text());h=json.loads((D/(name+'-head.json')).read_text())['sha']
 print(name,'rootdirs',[x['path'] for x in t['tree'] if x['type']=='tree' and '/' not in x['path']])
 for p in roots:
  x=next((x for x in t['tree'] if x['path']==p),None)
  if x:jobs.append([name+'-complete-'+p.replace('/','_')+'.json',f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1'])
 if name=='pool':
  for x in t['tree']:
   if x['type']=='blob' and re.search(r'(candidate|index|projects\.yml)',x['path'],re.I) and x.get('size',0)<500000 and re.search(r'\.(md|json|ya?ml)$',x['path']):jobs.append(['pool-index-'+hashlib.sha256(x['path'].encode()).hexdigest()[:12]+Path(x['path']).suffix,f'https://raw.githubusercontent.com/{repo}/{h}/{x["path"]}'])
(L/'target-plan.json').write_text(json.dumps(jobs));print('jobs',len(jobs))
v=json.loads((L/'versions.json').read_text());jobs=[]
for a,x in v.items():
 if len(x['versions'])>1:
  for n in x['versions'][:-1]:jobs.append([a+'v'+n+'.pdf','https://arxiv.org/pdf/'+a+'v'+n])
(L/'versions-plan.json').write_text(json.dumps(jobs))
