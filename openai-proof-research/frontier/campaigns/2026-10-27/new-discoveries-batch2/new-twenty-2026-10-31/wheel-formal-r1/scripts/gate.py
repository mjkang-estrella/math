import runpy,json,re
from pathlib import Path
D=Path(__file__).resolve().parent.parent
get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
for key,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('authors','Shivaramkratos/Ultimate_Independence_ratio_Python_Gurobi_code')]:
 h=json.loads((D/'sources'/f'{key}-head.json').read_text())
 root=json.loads(get(key+'-root.json',f"https://api.github.com/repos/{repo}/git/trees/{h['commit']['tree']['sha']}"))
 for e in root['tree']:
  if e['type']=='tree' and (e['path'] in ['D5','Problems','preprints'] or key=='authors'):
   b=get(key+'-'+e['path']+'.json',f"https://api.github.com/repos/{repo}/git/trees/{e['sha']}?recursive=1")
   if not b: continue
   t=json.loads(b)
   print(key,e['path'],'truncated',t.get('truncated'),'entries',len(t['tree']))
   hits=[x for x in t['tree'] if re.search(r'wheel|fractional.?chrom|2511.18747',x['path'],re.I)]
   print(json.dumps(hits,indent=2))
   for i,x in enumerate(hits):
    if x['type']=='blob':
     get(key+'-'+e['path']+'-hit'+str(i)+'.txt',f"https://raw.githubusercontent.com/{repo}/{h['sha']}/{e['path']}/{x['path']}")
 if key=='authors':
  for i,x in enumerate(root['tree']):
   if x['type']=='blob':
    get('authors-body'+str(i)+'.txt',f"https://raw.githubusercontent.com/{repo}/{h['sha']}/{x['path']}")
