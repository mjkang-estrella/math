import pathlib,subprocess,json,hashlib
from html.parser import HTMLParser
L=pathlib.Path(__file__).parent/'evidence'
class H(HTMLParser):
 def __init__(self):super().__init__();self.t=[]
 def handle_data(self,d):self.t.append(d)
for n in ['ohtsuki','calegari','wuthrich','aldous','cropping']:
 p=L/(n+'.body');m=json.loads((L/(n+'.provenance.json')).read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256']
 if p.read_bytes()[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(L/(n+'.txt'))],check=True)
 else:
  h=H();h.feed(p.read_text());(L/(n+'.txt')).write_text('\n'.join(h.t))
