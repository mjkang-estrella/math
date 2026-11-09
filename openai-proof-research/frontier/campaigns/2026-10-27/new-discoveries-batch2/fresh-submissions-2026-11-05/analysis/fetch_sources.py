from pathlib import Path
import requests,json,hashlib,concurrent.futures,subprocess,datetime
p=Path(__file__).parent;p.joinpath('sources').mkdir(exist_ok=True)
jobs={str(i):f'https://arxiv.org/pdf/{a}' for i,a in [(319645,'1003.1278'),(375970,'2607.10922'),(324961,'1302.1978'),(329722,'1501.05340'),(343381,'1907.12826'),(371416,'2511.08000')]};jobs['395581']='https://publications.mfo.de/bitstream/handle/mfo/3107/OWR_2009_06.pdf'
for repo in ['openai/math','trureturing/AutoMath']:jobs[repo.replace('/','-')]='https://api.github.com/repos/'+repo+'/commits/HEAD'
for i in [319645,375970,395581,324961,329722,371416]:jobs['live-'+str(i)]=f'https://mathdb.com/api/posts/{i}'
def go(k,u):
 try:
  r=requests.get(u,timeout=40);b=r.content;ext='pdf' if b.startswith(b'%PDF') else 'json';f=p/'sources'/f'{k}.{ext}';f.write_bytes(b)
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],capture_output=True,timeout=15)
  return dict(key=k,url=u,http_status=r.status_code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path=str(f),accessed=datetime.datetime.now(datetime.timezone.utc).isoformat())
 except Exception as e:return dict(key=k,url=u,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e:r=list(e.map(lambda z:go(*z),jobs.items()))
(p/'source-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
