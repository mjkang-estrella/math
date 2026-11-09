from urllib.request import urlopen
from pathlib import Path
from hashlib import sha256
import json,datetime
from html.parser import HTMLParser
class TextParser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.inmath=0
 def handle_starttag(self,t,a):
  if t=="math":self.parts.append(dict(a).get("alttext",""));self.inmath+=1
 def handle_endtag(self,t):
  if t=="math":self.inmath-=1
 def handle_data(self,d):
  if not self.inmath:self.parts.append(d)
root=Path(__file__).resolve().parents[1]/'sources'
urls={
'bbk':'https://arxiv.org/html/2601.04014v1',
'bbk-abs':'https://arxiv.org/abs/2601.04014',
'chern-wang':'https://arxiv.org/html/2601.19845v1',
'gatzweiler-krattenthaler':'https://arxiv.org/html/2502.06032v3',
'prellberg-stanton':'https://arxiv.org/html/2610.26878',
'yoshida':'https://arxiv.org/html/2603.22226',
'mathdb-372434':'https://mathdb.com/api/posts/372434',
}
records=[]
for name,url in urls.items():
 rec=dict(name=name,url=url,accessed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  r=urlopen(url,timeout=45);data=r.read();f=root/(name+'.html' if not name.startswith('mathdb') else name+'.json');f.write_bytes(data)
  rec.update(status=r.status,final_url=r.url,file=f.name,sha256=sha256(data).hexdigest())
  if f.suffix=='.html':
   parser=TextParser();parser.feed(data.decode());(root/(name+'.txt')).write_text(' '.join(parser.parts))
 except Exception as e:rec['error']=str(e)
 records.append(rec);(root/'manifest.json').write_text(json.dumps(records,indent=2))
 print(name,rec.get('status',rec.get('error')),flush=True)
