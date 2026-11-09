from pathlib import Path
import urllib.request,json,hashlib,datetime
L=Path(__file__).resolve().parent;log=json.loads((L/'source-provenance.json').read_text())
for name,url in [('fusion-categories.pdf','https://arxiv.org/pdf/math/0203060'),('formal-codegrees.pdf','https://arxiv.org/pdf/0810.0583'),('fusion-2.pdf','https://arxiv.org/pdf/1812.11933'),('morita-2.pdf','https://arxiv.org/pdf/2208.08722')]:
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'evidence/'+name,'role':'related primary context, not originating AIM body'}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read(14000000); e.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b));(L/e['file']).write_bytes(b)
 except Exception as ex:e['error']=str(ex)
 log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n'); print(e)
