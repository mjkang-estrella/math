import urllib.request,json,hashlib,pathlib,datetime,subprocess,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
w=pathlib.Path(__file__).resolve().parent;(w/'sources').mkdir(exist_ok=True)
urls={'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',**{i:'https://arxiv.org/pdf/'+i for i in ['2104.14516','2105.02018','2105.03890','2104.02786','2103.17147','2104.06959','2105.04137','2104.00778']}}
def fetch(kv):
 key,url=kv;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=30) as f:
   b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=f.url);ext='pdf' if b.startswith(b'%PDF') else 'json';p=w/'sources'/(key+'.'+ext);p.write_bytes(b);r['file']=str(p)
   if ext=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=20,check=True)
   else:r['head']=json.loads(b).get('sha')
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 receipts=list(ex.map(fetch,urls.items()))
(w/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(json.dumps(receipts,indent=2))
