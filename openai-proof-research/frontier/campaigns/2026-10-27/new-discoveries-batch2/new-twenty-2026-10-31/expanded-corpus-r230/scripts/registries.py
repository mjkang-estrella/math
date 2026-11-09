import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get,D
for key,repo in [('leanpool','Vilin97/lean-pool'),('openai','openai/math'),('omega','the-omega-institute/trureturing')]:
 print(get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD'),flush=True)
 p=D/'sources'/f'{key}-head.json'
 if p.exists():
  o=json.loads(p.read_text());sha=o.get('sha')
  if sha:print(get(key+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1'),flush=True)
