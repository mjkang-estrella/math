import urllib.request,urllib.error,json,hashlib,datetime,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(40,40));resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2)
r=Path(__file__).parent
urls={'trees.pdf':'https://dmtcs.episciences.org/12202/pdf','original.pdf':'https://arxiv.org/pdf/1805.06777','numbers.pdf':'https://arxiv.org/pdf/1810.04397','biased.pdf':'https://arxiv.org/pdf/2408.00529','critical.pdf':'https://arxiv.org/pdf/2503.11907','arxiv-source.html':'https://arxiv.org/abs/2206.12812','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','institution.html':'https://dirros.openscience.si/IzpisGradiva.php?id=20509&lang=eng'}
receipts=[]
for name,url in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-review'}),timeout=25) as q: data=q.read(20*1024**2);status=q.status;final=q.url
 except urllib.error.HTTPError as e:data=e.read();status=e.code;final=e.url
 except Exception as e:receipts.append({'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});continue
 (r/name).write_bytes(data);receipts.append({'url':url,'status':status,'final_url':final,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'file':name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
(r/'http-receipts.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
