from pathlib import Path
import urllib.request,hashlib,json,datetime
from html.parser import HTMLParser
L=Path(__file__).parent
class Parser(HTMLParser):
 def handle_data(self,data):
  if data.strip():self.out.write(data+'\n')
urls={'fu':'https://arxiv.org/html/2409.12404v1','filipi':'https://arxiv.org/html/2503.22377v1','kubjas':'https://arxiv.org/html/2402.00949v1','dao':'https://arxiv.org/html/2605.09609v1','fu-abs':'https://arxiv.org/abs/2409.12404','filipi-abs':'https://arxiv.org/abs/2503.22377'}
with (L/'http.jsonl').open('w') as log:
 for name,url in urls.items():
  row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   h=hashlib.sha256();n=0
   with urllib.request.urlopen(url,timeout=35) as r,(L/'inputs'/f'{name}.html').open('wb') as f:
    row['status']=r.status
    while b:=r.read(32768):f.write(b);h.update(b);n+=len(b)
   row.update(bytes=n,sha256=h.hexdigest())
   p=Parser()
   with (L/'inputs'/f'{name}.txt').open('w') as out,(L/'inputs'/f'{name}.html').open() as f:
    p.out=out
    while b:=f.read(32768):p.feed(b)
  except Exception as e:row['error']=str(e)
  log.write(json.dumps(row)+'\n');log.flush();print(json.dumps(row),flush=True)
