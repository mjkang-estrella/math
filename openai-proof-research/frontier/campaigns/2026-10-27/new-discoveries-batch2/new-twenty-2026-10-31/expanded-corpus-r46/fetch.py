import urllib.request,urllib.error,pathlib,json,hashlib,datetime,resource,concurrent.futures,subprocess
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3)); resource.setrlimit(resource.RLIMIT_CPU,(90,90))
p=pathlib.Path(__file__).resolve().parent; (p/'sources').mkdir(exist_ok=True)
urls={x:'https://arxiv.org/pdf/'+x for x in ['2201.03865','2201.08464','2202.01867','2112.12716','2111.11162','2202.05562','2111.15303','2202.01948']};urls.update({'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'})
def fetch(k,u):
 rec={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-review/1.0'}),timeout=35) as r:
   data=r.read(15*1024**2); rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)); ext='.pdf' if data.startswith(b'%PDF') else '.json';f=p/'sources'/(k+ext);f.write_bytes(data)
   if ext=='.pdf': subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=20,check=True)
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 (p/'sources'/(k+'-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(k,rec)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(lambda kv:fetch(*kv),urls.items()))
