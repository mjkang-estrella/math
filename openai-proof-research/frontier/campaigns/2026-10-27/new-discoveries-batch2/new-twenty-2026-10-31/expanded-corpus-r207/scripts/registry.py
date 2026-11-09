import json,importlib.util,time,urllib.parse
from pathlib import Path
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',L/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
out={}
for name,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 if name=='pool': b=next((L/'sources').glob('lean-pool-head-*/body')).read_bytes()
 else: b,_,_=f.fetch(f'https://api.github.com/repos/{repo}/commits/HEAD',name+'-head')
 try: sha=json.loads(b)['sha']
 except Exception: continue
 b,r,p=f.fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1',name+'-tree'); out[name]={'head':sha,'tree_receipt':p}
 try: tree=json.loads(b)['tree']
 except Exception: continue
 if name=='pool':
  files=[x['path'] for x in tree if x['type']=='blob' and (x['path']=='projects.yml' or x['path'].startswith('candidates/'))]
  out[name]['files']=[]
  for path in files:
   body,rec,folder=f.fetch(f'https://raw.githubusercontent.com/{repo}/{sha}/{path}','pool-file');out[name]['files'].append({'path':path,'receipt':folder})
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
