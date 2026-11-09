from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,resource,concurrent.futures,time,re,sys,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
def get(url):
 name=re.sub(r'[^a-zA-Z0-9._-]','_',url.removeprefix('https://'));f=p/'sources'/name
 d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(f.relative_to(p))}
 try:
  with urllib.request.urlopen(url,timeout=18) as r:
   b=r.read(30*1024**2);d.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));f.write_bytes(b)
  if b.startswith(b'%PDF'):
   t=Path(str(f)+'.txt');q=subprocess.run(['pdftotext','-layout',str(f),str(t)],capture_output=True,timeout=15);d.update(text_path=str(t.relative_to(p)),pdftotext_returncode=q.returncode)
 except Exception as e:d.update(error=str(e))
 return d
if sys.argv[1]=='abs':
 d=json.loads((p/'extracted.json').read_text());urls=sorted({x['record']['source_url'] for x in d.values()}|{'https://arxiv.org/abs/math/0703888','https://arxiv.org/abs/1105.2389','https://arxiv.org/abs/1904.02694','https://arxiv.org/abs/1102.2480'})
else:urls=(p/sys.argv[1]).read_text().splitlines()
start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:r=list(ex.map(get,urls))
out=p/('receipts-'+sys.argv[1].replace('.txt','')+'.json');out.write_text(json.dumps(r,indent=2)+'\n')
for x in r:print(x['url'],x.get('status'),x.get('error',''),x.get('bytes',''))
print('completed wall',time.monotonic()-start,'CPU',time.process_time(),'maxrss',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
