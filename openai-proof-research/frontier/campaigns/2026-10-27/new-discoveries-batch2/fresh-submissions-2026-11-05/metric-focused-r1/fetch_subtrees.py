import requests,json,hashlib,time
from pathlib import Path
p=Path(__file__).parent; receipts=[]
def get(url,name):
 r=requests.get(url,timeout=45);r.raise_for_status();(p/name).write_bytes(r.content);receipts.append(dict(url=url,path=name,status=r.status_code,sha256=hashlib.sha256(r.content).hexdigest()));return r.json()
for label,repo,subtrees in [('openai','openai/math',['preprints','lean']),('omega','the-omega-institute/trureturing',['Problems','Library','Reg','Evidence'])]:
 root=json.loads((p/(label+'-head-root.json')).read_text());matches=[];stats=[]
 def walk(sha,prefix):
  name=label+'-subtree-'+prefix.replace('/','_')+'.json';j=get(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1',name)
  stats.append(dict(prefix=prefix,truncated=j.get('truncated'),entries=len(j.get('tree',[]))))
  if j.get('truncated'):
   nr=get(f'https://api.github.com/repos/{repo}/git/trees/{sha}',name+'.root.json')
   for e in nr['tree']:
    if e['type']=='tree':walk(e['sha'],prefix+'/'+e['path'])
    else:matches.append(dict(path=prefix+'/'+e['path'],sha=e['sha']))
  else:
   matches.extend(dict(path=prefix+'/'+e['path'],sha=e['sha']) for e in j['tree'] if e['type']=='blob')
 for t in subtrees:
  e=next(x for x in root['tree'] if x['path']==t);walk(e['sha'],t)
 (p/(label+'-complete-paths.json')).write_text(json.dumps(matches))
 (p/(label+'-subtree-stats.json')).write_text(json.dumps(stats,indent=2));print(label,len(matches),stats,flush=True)
(p/'subtree-receipts.json').write_text(json.dumps(receipts,indent=2))
