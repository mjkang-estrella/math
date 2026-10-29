import urllib.request,json,hashlib,datetime
from pathlib import Path
O=Path(__file__).parent; (O/'evidence').mkdir(exist_ok=True)
items={'relosc':'https://www.mat.univie.ac.at/~gerald/ftp/articles/RelOsc2.pdf','distsl':'https://www.mat.univie.ac.at/~gerald/ftp/articles/DistSL.pdf','nagy':'https://users.math.msu.edu/users/gnagy/teaching/ade.pdf','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/dev','kvz-history':'https://arxiv.org/abs/2408.01755','kvz-final':'https://link.springer.com/content/pdf/10.1007/s00025-025-02431-4.pdf'}
for name,url in items.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-review/1.0'}),timeout=25) as h:
   data=h.read(); r.update(status=h.status,final_url=h.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)); (O/'evidence'/(name+('.pdf' if data.startswith(b'%PDF') else '.json' if 'api.github' in url else '.html'))).write_bytes(data)
 except Exception as e:r['error']=str(e)
 with (O/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
