from pathlib import Path
import json,urllib.request,hashlib,datetime
P=Path(__file__).resolve().parent;log=json.loads((P/'http.json').read_text())
def get(n,u):
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();s=r.status
  f='sources/'+n;(P/f).write_bytes(b);log.append(dict(url=u,status=s,file=f,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));return json.loads(b)
 except Exception as e:log.append(dict(url=u,error=str(e)))
h=json.loads((P/'sources/omega-head.json').read_text())['sha'];o=json.loads((P/'sources/openai-head.json').read_text())['sha'];print('heads',h,o)
d=get('omega-delta.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/28414a3d55d5b97458b138701407d5678e167a8e...'+h)
print('delta',d.get('total_commits'),len(d.get('files',[])))
for i,x in enumerate(d.get('files',[])):
 if x['status']=='removed':continue
 u='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+urllib.parse.quote(x['filename'])
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read()
  f='sources/omega-delta-body-'+str(i)+'.txt';(P/f).write_bytes(b);log.append(dict(url=u,status=200,file=f,sha256=hashlib.sha256(b).hexdigest()));print(x['filename'],len(b))
 except Exception as e:log.append(dict(url=u,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2))
