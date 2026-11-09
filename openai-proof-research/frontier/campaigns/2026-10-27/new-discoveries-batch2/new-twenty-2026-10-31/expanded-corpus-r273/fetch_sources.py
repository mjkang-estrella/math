import requests,json,hashlib,datetime,resource,concurrent.futures,subprocess,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
r=json.loads((p/'reservation.json').read_text())
def job(row):
 id=row['mathdb_id'];u=row['source_url'];out=[]
 for kind,url in [('abs',u),('pdf',u.replace('/abs/','/pdf/'))] if 'arxiv' in u else [('page',u)]:
  receipt={'id':id,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   a=requests.get(url,timeout=10);b=a.content;receipt.update(status=a.status_code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=a.url)
   f=s/f'{id}.{kind}';f.write_bytes(b)
   if kind=='pdf' and a.status_code==200 and b.startswith(b'%PDF'):
    z=subprocess.run(['pdftotext','-layout',str(f),str(s/f'{id}.txt')],capture_output=True,text=True,timeout=15);receipt['pdftotext_returncode']=z.returncode
  except Exception as e:receipt['error']=str(e)
  (s/f'{id}.{kind}.receipt.json').write_text(json.dumps(receipt,indent=2));out.append(receipt)
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for out in pool.map(job,r['rows']):print(json.dumps(out),flush=True)
