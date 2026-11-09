from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
P=Path(__file__).parent
out=[]
for name,url in [('kings','https://arxiv.org/pdf/math/0608140v1'),('independent','https://arxiv.org/pdf/math/0309441v1'),('interpolation','https://arxiv.org/pdf/0912.2444v2'),('rainbow','https://arxiv.org/pdf/2212.04640v1')]:
 d={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Mozilla/5.0','Accept':'application/pdf'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=d['headers']),timeout=25) as r:
   b=r.read();d.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b))
   assert b.startswith(b'%PDF')
   (P/(name+'.pdf')).write_bytes(b)
 except Exception as e:d['failure']=str(e)
 out.append(d)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
