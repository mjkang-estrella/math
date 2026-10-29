from pathlib import Path
import urllib.request,json,hashlib,datetime
P=Path(__file__).resolve().parent; S=P/'sources'; log=[]
urls={
'smith.html':'https://arxiv.org/html/2511.22814v2',
'smith-abs.html':'https://arxiv.org/abs/2511.22814',
'bow.html':'https://arxiv.org/html/2409.03859',
'bow-abs.html':'https://arxiv.org/abs/2409.03859',
'precursive.html':'https://arxiv.org/html/2511.02121',
'precursive-abs.html':'https://arxiv.org/abs/2511.02121',
'omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
for name,url in urls.items():
 try:
  r=urllib.request.urlopen(url,timeout=25);b=r.read();(S/name).write_bytes(b);row={'file':'sources/'+name,'url':url,'status':r.status,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'time':datetime.datetime.now(datetime.timezone.utc).isoformat()};print(name,len(b),flush=True)
 except Exception as e:row={'url':url,'error':str(e)};print(name,e,flush=True)
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2))
