from pathlib import Path
import concurrent.futures,datetime,hashlib,json,subprocess,requests
from html.parser import HTMLParser
class TextParser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,data):self.parts.append(data)
 def get_text(self):return "\n".join(self.parts)
def html_text(b):
 p=TextParser();p.feed(b.decode(errors="replace"));return p.get_text()
S=Path(__file__).resolve().parents[2]/'sources/i24_elementary_unimodality/literature';S.mkdir(parents=True,exist_ok=True)
items={'dm-abs':'https://arxiv.org/abs/1910.12915','sw-abs':'https://arxiv.org/abs/1405.4629','tom-abs':'https://arxiv.org/abs/2311.08020','abreu-nigro-abs':'https://arxiv.org/abs/2006.00657','cho-huh-abs':'https://arxiv.org/abs/1711.07152','huh-nam-yoo-abs':'https://arxiv.org/abs/1812.03445','dm-v3':'https://arxiv.org/html/1910.12915v3','sw-v2':'https://arxiv.org/pdf/1405.4629v2','tom-v2':'https://arxiv.org/html/2311.08020v2','abreu-nigro-v2':'https://arxiv.org/pdf/2006.00657v2','cho-huh':'https://arxiv.org/pdf/1711.07152','huh-nam-yoo':'https://arxiv.org/pdf/1812.03445','icm-davison':'https://epubs.siam.org/doi/10.1137/25M1810234','icm-abs':'https://arxiv.org/abs/2601.08004','icm-v1':'https://arxiv.org/pdf/2601.08004v1','log-concavity-abs':'https://arxiv.org/abs/2607.20595'}
def get(item):
 name,url=item
 try:
  r=requests.get(url,timeout=50);b=r.content; ext='pdf' if b.startswith(b'%PDF') else 'html';p=S/(name+'.'+ext);p.write_bytes(b)
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(S/(name+'.txt'))],check=True)
  else:(S/(name+'.txt')).write_text(html_text(b))
  return dict(name=name,url=url,final_url=r.url,status=r.status_code,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),file=str(p.relative_to(S)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:return dict(name=name,url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: rows=list(pool.map(get,items.items()))
(S/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
