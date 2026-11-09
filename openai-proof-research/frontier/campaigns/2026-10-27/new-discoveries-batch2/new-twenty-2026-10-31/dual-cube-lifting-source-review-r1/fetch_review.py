import urllib.request,hashlib,concurrent.futures
urls=[('qin2020','https://doi.org/10.1109/TPDS.2019.2931904'),('main-abs','https://arxiv.org/abs/2607.25917'),('companion-abs','https://arxiv.org/abs/2608.00900'),('main-v2','https://arxiv.org/html/2607.25917v2'),('openai-head','https://github.com/openai/math'),('leanpool-head','https://github.com/LeanPool/lean-pool'),('qin2022','https://cis.temple.edu/~jiewu/research/publications/Publication_files/Construction_of_Dual-CISTs_on_an_Infinite_Class_of_Networks.pdf')]
def fetch(item):
 key,url=item;r=dict(key=key,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());t=time.monotonic()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source review'}),timeout=20) as resp:
   data=resp.read(12*1024*1024+1)
   if len(data)>12*1024*1024:raise ValueError('byte cap')
   r.update(status=resp.status,final_url=resp.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(p/(key+('.pdf' if key=='qin2022' else '.html'))).write_bytes(data)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['elapsed']=time.monotonic()-t;return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 results=list(ex.map(fetch,urls))
with (p/'http-receipts.jsonl').open('a') as f:
 for r in results:f.write(json.dumps(r)+'\n');print(json.dumps(r))
