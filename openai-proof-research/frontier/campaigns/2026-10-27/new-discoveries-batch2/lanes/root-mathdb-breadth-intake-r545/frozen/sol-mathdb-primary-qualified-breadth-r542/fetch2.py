from pathlib import Path
import urllib.request,json,hashlib,datetime
O=Path(__file__).resolve().parent;out=[]
for name,url in [('blocks-latest','https://arxiv.org/html/2302.13147'),('intersect-latest','https://arxiv.org/html/2604.10928'),('oeis','https://oeis.org/A274199/internal')]:
 a={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as resp:
   b=resp.read();p=O/(name+'.html');p.write_bytes(b);a.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b),status=resp.status,final_url=resp.url)
 except Exception as e:a['failure']=str(e)
 out.append(a)
(O/'retrieval2-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
