import pathlib,json
L=pathlib.Path(__file__).resolve().parent;d=json.loads((L/'openai-complete-lean.body').read_text());j=[]
for e in d['tree']:
 if e['type']=='tree' and e['path'].count('/')<2 and (e['path']=='OAI' or any(s in e['path'] for s in ['Combin','Graph','Dynamics','Number'])):
  print(e['path']);j.append(('openai-narrow-'+e['path'].replace('/','-'),'https://api.github.com/repos/openai/math/git/trees/'+e['sha']))
# fetch all actual section proof bodies of two lexical collisions for scope examination
for name,u in json.loads((L/'matched-jobs.json').read_text()):
 if '/sections/' in u:j.append((name,u))
(L/'narrow-jobs.json').write_text(json.dumps(j))
