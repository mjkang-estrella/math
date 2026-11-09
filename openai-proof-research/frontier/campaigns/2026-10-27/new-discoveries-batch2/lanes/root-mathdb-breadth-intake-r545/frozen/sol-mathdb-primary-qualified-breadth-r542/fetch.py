from pathlib import Path
import urllib.request,json,hashlib,datetime
O=Path(__file__).resolve().parent
out=[]
for name,id in [('apn','2407.11783'),('blocks','2302.13147'),('eggs','2511.18330'),('fingerhut','2212.14200'),('intersect','2604.10928')]:
 url='https://arxiv.org/html/'+id+'v1';a={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as resp:
   b=resp.read();p=O/(name+'.html');p.write_bytes(b);a.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b),status=resp.status,final_url=resp.url)
 except Exception as e:a['failure']=str(e)
 out.append(a)
(O/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
