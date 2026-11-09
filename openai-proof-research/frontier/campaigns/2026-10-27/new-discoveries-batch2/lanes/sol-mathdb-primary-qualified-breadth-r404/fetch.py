from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
L=Path(__file__).resolve().parent; (L/'evidence').mkdir(exist_ok=True)
urls=[('kourovka.pdf','https://alglog.org/21tkt.pdf'),('bakers.html','https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/14-01/'),('bestvina.pdf','https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf')]
log=[]
for name,url in urls:
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'evidence/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source review'}),timeout=25) as r:
   b=r.read(16000000);e.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b));(L/e['file']).write_bytes(b)
 except Exception as ex:e['error']=str(ex)
 log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
 print(e)
