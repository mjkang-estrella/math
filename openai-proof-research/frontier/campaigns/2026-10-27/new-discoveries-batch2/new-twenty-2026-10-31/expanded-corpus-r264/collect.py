from pathlib import Path
import json,hashlib,datetime,urllib.request,concurrent.futures,resource,subprocess,re,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; data=json.loads((p/'literal-provenance.json').read_text()); (p/'sources').mkdir(exist_ok=True)
def job(item):
 i,x=item; url=x['record']['source_url']; aid=url.split('/abs/')[-1]; urls=[('abs',url),('pdf','https://arxiv.org/pdf/'+aid)] if 'arxiv' in url else [('abs',url)]
 receipts=[]
 for kind,u in urls:
  rec={'id':i,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}; f=p/'sources'/f'{i}.{kind}'
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source review'}),timeout=22) as r: b=r.read(15000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));f.write_bytes(b)
   if kind=='pdf' and b.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(f),str(p/'sources'/f'{i}.txt')],timeout=20,check=True)
  except Exception as e: rec['error']=str(e)
  receipts.append(rec)
 return receipts
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 rows=list(ex.map(job,data.items()))
(p/'source-receipts.json').write_text(json.dumps(sum(rows,[]),indent=2));print(json.dumps(sum(rows,[]),indent=2))
