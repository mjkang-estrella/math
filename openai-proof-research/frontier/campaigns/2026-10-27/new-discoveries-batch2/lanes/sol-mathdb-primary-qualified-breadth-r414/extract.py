from pathlib import Path
import json,hashlib,subprocess,gzip
from html.parser import HTMLParser
R=Path(__file__).resolve().parent/'primary'
class P(HTMLParser):
 def __init__(self):super().__init__();self.t=[];self.links=[]
 def handle_data(self,d):self.t.append(d)
 def handle_starttag(self,t,a):
  if t=='a':self.links.append(dict(a).get('href',''))
for p in R.iterdir():
 if '.' in p.name:continue
 m=json.loads((R/(p.name+'.meta.json')).read_text());d=p.read_bytes();assert hashlib.sha256(d).hexdigest()==m['sha256']
 if d.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(R/(p.name+'.txt'))],check=True)
 elif d.startswith(b'\x1f\x8b'):
  q=R/(p.name+'.ps');q.write_bytes(gzip.decompress(d));subprocess.run(['ps2ascii',str(q),str(R/(p.name+'.txt'))],check=True)
 else:
  a=P();a.feed(d.decode(errors='replace'));(R/(p.name+'.txt')).write_text('\n'.join(a.t));(R/(p.name+'.links.json')).write_text(json.dumps(a.links,indent=2))
 print(p.name,'extracted')
