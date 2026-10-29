import urllib.request,json,hashlib,datetime,resource,signal,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(55)
r=Path(__file__).parent;d=r/'live';d.mkdir(exist_ok=True)
urls={'arxiv':'https://arxiv.org/abs/2505.10501','author':'https://people.math.sc.edu/cooper/','qi.pdf':'https://www.polyu.edu.hk/ama/staff/new/qilq/qi-eigen-1.pdf','omega':'https://api.github.com/repos/the-omega-institute/trureturing/commits/dev','omega-main':'https://api.github.com/repos/the-omega-institute/trureturing/commits/main','openai':'https://api.github.com/repos/openai/math/commits/main','aim':'https://api.github.com/repos/MColbrook/AIM/commits/main','count':'https://api.github.com/repos/suvrit/count-ex-machina/git/trees/main'}
rows=[]
for name,url in urls.items():
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent-mathematical-review/1.0'}),timeout=10) as f:
   b=f.read(8*1024**2);status=f.status;final=f.url
  (d/name).write_bytes(b);rows.append({'utc':t,'url':url,'file':'live/'+name,'status':status,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'final_url':final})
 except Exception as e:rows.append({'utc':t,'url':url,'error':str(e),'retry':False})
(r/'live-http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
