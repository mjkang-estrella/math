import urllib.request,urllib.error,json,hashlib,datetime
from pathlib import Path
p=Path(__file__).parent;p.joinpath('sources').mkdir(exist_ok=True)
records=[];blocked=set()
for name,url in [('bbk.html','https://arxiv.org/html/2601.04014v1'),('chern.html','https://arxiv.org/html/2601.19845v1'),('liu.html','https://arxiv.org/html/2605.28012v1'),('mathdb.html','https://mathdb.com/p/372434/partial-fraction-positivity-conjecture-for-g-k-n-q')]:
 host=urllib.parse.urlparse(url).netloc
 if host in blocked:continue
 r={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(4000000);r['status']=f.status
  if any(x in b.lower() for x in [b'cf-chl-',b'just a moment...',b'captcha']):blocked.add(host);r['challenge']=True
  p.joinpath('sources',name).write_bytes(b);r.update(file=name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except urllib.error.HTTPError as e:
  r['status']=e.code
  if e.code in (403,429):blocked.add(host)
 except Exception as e:r['error']=str(e)
 records.append(r)
p.joinpath('retrieval.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records))
