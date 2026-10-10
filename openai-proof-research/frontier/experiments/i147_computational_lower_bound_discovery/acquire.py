import json,hashlib,urllib.request,urllib.error,datetime,concurrent.futures
from pathlib import Path
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0;self.math=0
 def handle_starttag(self,tag,attrs):
  if tag in ('script','style'):self.skip+=1
  if tag=='math':
   self.math+=1;self.parts.append(dict(attrs).get('alttext','[math]'))
  if tag in ('p','div','section','h1','h2','h3','h4','h5','h6','li','tr','br'):self.parts.append('\n')
 def handle_endtag(self,tag):
  if tag in ('script','style'):self.skip-=1
  if tag=='math':self.math-=1
  if tag in ('p','div','section','li','tr'):self.parts.append('\n')
 def handle_data(self,data):
  if not self.skip and not self.math:self.parts.append(data)
 def text(self):return '\n'.join(x.strip() for x in ''.join(self.parts).splitlines() if x.strip())

S=Path('frontier/sources/i147_computational_lower_bound_discovery');(S/'external').mkdir(exist_ok=True)
items=[('ggj-v2','https://arxiv.org/html/2604.02793v2'),('jtvw-v4','https://arxiv.org/html/2512.14643v4'),('gaussian-v2','https://arxiv.org/html/2110.10801v2'),('transitive','https://dmtcs.episciences.org/15992/pdf')]
def get(item):
 name,url=item
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I147 research source retrieval'}),timeout=60) as r: b=r.read();status=r.status;ctype=r.headers.get('Content-Type');final=r.url
 except urllib.error.HTTPError as e: b=e.read();status=e.code;ctype=e.headers.get('Content-Type');final=e.url
 ext='pdf' if b.startswith(b'%PDF') else 'html';p=S/'external'/f'{name}.{ext}';p.write_bytes(b)
 row=dict(url=url,final_url=final,status=status,content_type=ctype,path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 if status==200 and ext=='html':
  parser=Text();parser.feed(b.decode('utf-8'));txt=parser.text();q=p.with_suffix('.txt');q.write_text(txt,encoding='utf-8');row['text']=str(q);row['normalization']='stdlib HTMLParser; entities decoded; skip script/style and MathML children; math alttext; block LF; strip lines and discard empty lines; UTF8 no terminal LF' 
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: rows=list(pool.map(get,items))
(S/'http-log.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
