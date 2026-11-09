from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,sys,subprocess
L=Path(__file__).resolve().parent
def get(name,url,pdf=False):
 (L/'primary').mkdir(exist_ok=True)
 row={'url':url,'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=35) as f:
   b=f.read(8000001);row.update(status=f.status,final_url=f.url)
  assert len(b)<=8000000
  assert not any(s in b[:15000].lower() for s in [b'captcha',b'cf-chl-',b'verify you are human'])
  if pdf:assert b.startswith(b'%PDF')
  p=L/'primary'/name;q=L/'frozen'/name;p.write_bytes(b);q.write_bytes(b)
  h=hashlib.sha256(b).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()==h
  row.update(sha256=h,original=str(p),copy=str(q),bytes=len(b))
  if pdf:
   subprocess.run(['pdftotext','-layout',str(q),str(q.with_suffix('.txt'))],check=True)
   row['text_sha256']=hashlib.sha256(q.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e:row['error']=repr(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row))
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2],sys.argv[1].endswith('.pdf'))
 else:
  for name,q in [('specialist.xml','all:"finite free" AND (all:submodularity OR all:Horn OR all:interior)'),('leake.xml','au:"Jonathan_Leake" AND all:convolution')]:
   get(name,'https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':60,'sortBy':'submittedDate','sortOrder':'descending'}))
