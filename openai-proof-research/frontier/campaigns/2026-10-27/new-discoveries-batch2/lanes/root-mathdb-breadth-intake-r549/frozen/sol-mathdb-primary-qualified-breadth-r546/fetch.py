from pathlib import Path
import urllib.request,hashlib,json,datetime
P=Path(__file__).resolve().parent
out=[]
for key,url in [('groupoid','https://arxiv.org/html/1410.7501v1'),('morita','https://arxiv.org/html/1801.06072v1'),('matroids','https://arxiv.org/html/1712.07702v1'),('codes','https://arxiv.org/html/1707.03285v1'),('zeros','https://arxiv.org/html/2507.05732v1'),('grid','https://arxiv.org/html/2112.08768v1')]:
 r={'key':key,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();r['final_url']=f.url;r['status']=f.status
  (P/(key+'.html')).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),path=key+'.html')
 except Exception as e:r.update(error=str(e),stopped=True)
 out.append(r);print(key,r.get('status',r.get('error')))
 (P/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
