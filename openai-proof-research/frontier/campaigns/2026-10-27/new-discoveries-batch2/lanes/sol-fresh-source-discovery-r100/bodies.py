from pathlib import Path
import urllib.request,json,hashlib
P=Path(__file__).resolve().parent;S=P/'sources';d=json.loads((P/'registry.json').read_text());log=[]
paths=[('omega',p) for p in d['omega']['matches']]+[('openai',p) for p in d['openai']['matches']]
for i,(key,path) in enumerate(paths):
 repo='the-omega-institute/trureturing' if key=='omega' else 'openai/math';u='https://raw.githubusercontent.com/'+repo+'/'+d[key]['head']+'/'+path
 try:
  r=urllib.request.urlopen(u,timeout=25);b=r.read();n='registry-body-'+str(i)+Path(path).suffix;(S/n).write_bytes(b);log.append({'file':'sources/'+n,'path':path,'url':u,'status':r.status,'sha256':hashlib.sha256(b).hexdigest()});print(n,len(b),flush=True)
 except Exception as e:log.append({'path':path,'url':u,'error':str(e)});print(e,flush=True)
(P/'registry-bodies-http.json').write_text(json.dumps(log,indent=2))
