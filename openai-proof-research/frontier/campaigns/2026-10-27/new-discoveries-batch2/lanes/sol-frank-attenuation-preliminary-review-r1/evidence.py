from pathlib import Path
import json,urllib.request,urllib.error,datetime,hashlib,sys
from html.parser import HTMLParser
L=Path(__file__).resolve().parent
if len(sys.argv)>1:
 url=sys.argv[1];name=sys.argv[2]
 try:
  with urllib.request.urlopen(url,timeout=30) as r: data=r.read(4000000);status=r.status
 except urllib.error.HTTPError as e: data=e.read(4000000);status=e.code
 (L/name).write_bytes(data)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),url=url,status=status,path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))+'\n')
else:
 class Parser(HTMLParser):
  def __init__(self):super().__init__();self.skip=0;self.parts=[]
  def handle_starttag(self,t,a):
   if t in ['script','style']:self.skip+=1
  def handle_endtag(self,t):
   if t in ['script','style']:self.skip-=1
  def handle_data(self,d):
   if not self.skip and d.strip():self.parts.append(d.strip())
 for name in ['frank','polyserial-pmc']:
  p=Parser();p.feed((L/'inputs/sources'/ (name+'.html')).read_text())
  (L/(name+'-read.txt')).write_text('\n'.join(p.parts))
 print('extracted source bodies')
