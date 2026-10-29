from review_tools import *
import urllib.request,urllib.error,subprocess,re
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):
  if d.strip():self.a.append(d.strip())
def get(url,name):
 utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source review'}),timeout=30) as f:raw=f.read(8000000);status=f.status
  (R/name).write_bytes(raw);rec=dict(url=url,utc=utc,status=status,path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 except urllib.error.HTTPError as e:rec=dict(url=url,utc=utc,status=e.code,error=str(e));raw=None
 with (R/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
 if rec['status'] in [403,429]:sys.exit(0)
 return raw
for url,name in [
 ('https://arxiv.org/pdf/1509.00131','separating.pdf'),
 ('https://perso.limos.fr/ffoucaud/Publications/Papers/J17_LD-line_DM_2017.pdf','locating.pdf'),
 ('https://raw.githubusercontent.com/the-omega-institute/trureturing/7f200dc4fad796eec490994c705245530200fd78/Blueprint/D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.md','registry-hamming.md')]:
 if get(url,name) and name.endswith('.pdf'):
  subprocess.run(['pdftotext','-layout',str(R/name),str(R/name.replace('.pdf','.txt'))],check=True)
for name in ['separating.txt','locating.txt','registry-hamming.md']:
 p=R/name
 if p.exists():
  lines=p.read_text().splitlines();print('\nSOURCE',name)
  if name=='registry-hamming.md':print(p.read_text()[:6500]);continue
  shown=0
  for i,l in enumerate(lines):
   if re.search(r'Theorem [125]|2-separating|locating if|union|non-adaptive|k = 2|k=2',l):
    print('\n'.join(lines[max(0,i-3):i+19]));shown+=1
    if shown==9:break
p=Parser();p.feed((R/'multiset-body.html').read_text());text=' '.join(p.a)
needle='multiset signature';i=text.find(needle)
excerpt=text[max(0,i-120):i+4800] if i>=0 else text[:5500]
(R/'multiset-excerpt.txt').write_text(excerpt);print('MULTISET',excerpt)
