from pathlib import Path
import urllib.request,hashlib,json,datetime
from html.parser import HTMLParser
P=Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,t):self.out.append(t)
records=[]
for id in ['2607.08869','2609.08612','2609.13517']:
 for form in ['abs','html']:
  url=f'https://arxiv.org/{form}/{id}';r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=25) as s:
    b=s.read(8000000);r.update(status=s.status,headers=dict(s.headers))
   f=P/'sources'/f'{id}-{form}.html';f.write_bytes(b);r.update(file=str(f.relative_to(P)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
   t=Text();t.feed(b.decode());f.with_suffix('.txt').write_text('\n'.join(t.out))
  except Exception as e:r['error']=repr(e)
  records.append(r);(P/'http.json').write_text(json.dumps(records,indent=2))
print([(r['url'],r.get('status'),r.get('error')) for r in records])
