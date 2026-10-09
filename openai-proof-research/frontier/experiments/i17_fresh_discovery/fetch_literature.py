from pathlib import Path
import urllib.request,json,hashlib,datetime
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self): super().__init__(); self.parts=[];self.links=[]
 def handle_data(self,data):
  if data.strip():self.parts.append(data.strip())
 def handle_starttag(self,tag,attrs):
  if tag=="a": self.links.append(dict(attrs).get("href",""))
BASE=Path(__file__).resolve().parents[3]; OUT=BASE/'frontier/sources/i17_fresh_discovery/literature';OUT.mkdir(exist_ok=True)
items=[('palvolgyi-2609.23327-abs','https://arxiv.org/abs/2609.23327','latest abstract checked; v1 2026-09-20'),('palvolgyi-2609.23327v1','https://arxiv.org/html/2609.23327v1','arXiv v1, 2026-09-20'),('bessenrodt-bowman-2023','https://alco.centre-mersenne.org/articles/10.5802/alco.294/','published Algebraic Combinatorics 6(4), 2023, 863-898'),('randolph-wegrzycki-2511.10823-abs','https://arxiv.org/abs/2511.10823','latest abstract retrieval'),('cheng-liu-shao-xu-2609.07446-abs','https://arxiv.org/abs/2609.07446','latest abstract retrieval')]
items += [('bessenrodt-bowman-2202.03066-abs','https://arxiv.org/abs/2202.03066','latest abstract checked; v3'),('bessenrodt-bowman-2202.03066v3','https://arxiv.org/html/2202.03066v3','arXiv v3'),('chen-dey-panchenko-1509.07071-abs','https://arxiv.org/abs/1509.07071','latest abstract retrieval'),('chen-dey-panchenko-1509.07071v2','https://arxiv.org/html/1509.07071v2','arXiv v2'),('randolph-wegrzycki-2511.10823v1','https://arxiv.org/html/2511.10823v1','arXiv v1; check current abstract separately')]
manifest=[]
for name,url,version in items:
 try:
  with urllib.request.urlopen(url,timeout=60) as r: b=r.read();final=r.url
 except Exception as e:
  manifest.append(dict(name=name,url=url,version=version,error=str(e)));print(name,str(e));continue
 p=OUT/(name+'.html');p.write_bytes(b)
 soup=Parser();soup.feed(b.decode());txt='\n'.join(soup.parts);q=OUT/(name+'.txt');q.write_text(txt)
 manifest.append(dict(name=name,url=url,final_url=final,version=version,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),file=str(p.relative_to(BASE)),sha256=hashlib.sha256(b).hexdigest(),text_file=str(q.relative_to(BASE)),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
 print(name,len(b))
 if name=='bessenrodt-bowman-2023':
  print('arxiv links',[a for a in soup.links if 'arxiv' in a])
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
