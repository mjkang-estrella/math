from pathlib import Path
import json,urllib.request,urllib.error,hashlib,datetime,concurrent.futures,resource,subprocess
P=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
jobs=[('abm-v1','https://arxiv.org/pdf/1312.4487v1'),('abm-v2','https://arxiv.org/pdf/1312.4487v2'),('abm-v3','https://arxiv.org/pdf/1312.4487v3'),('secondary-v2','https://arxiv.org/pdf/1510.00777v2'),('abm-journal','https://www.sciencedirect.com/science/article/pii/S0195669814001541/pdfft'),('secondary-journal','https://www.sciencedirect.com/science/article/pii/S0195669816300841/pdfft')]+[(n+'-head','https://api.github.com/repos/'+repo+'/commits/HEAD') for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]]
def get(job):
 n,url=job;rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'SourceQualification/1.0'})
  with urllib.request.urlopen(req,timeout=22) as res: body=res.read(30000000);rec.update(status=res.status,final_url=res.url,content_type=res.headers.get('Content-Type'))
 except urllib.error.HTTPError as e: body=e.read();rec.update(status=e.code,error=str(e))
 except Exception as e: body=b'';rec.update(status=None,error=str(e))
 rec.update(bytes=len(body),sha256=hashlib.sha256(body).hexdigest());(P/(n+'.body')).write_bytes(body);(P/(n+'.receipt.json')).write_text(json.dumps(rec,indent=2))
 if body.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(P/(n+'.body')),str(P/(n+'.txt'))],check=True,timeout=12)
 return n,rec
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
  for n,r in ex.map(get,jobs): print(n,r)
