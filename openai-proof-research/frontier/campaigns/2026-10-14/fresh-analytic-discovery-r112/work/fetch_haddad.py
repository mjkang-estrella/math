from pathlib import Path
import urllib.request,json,hashlib,subprocess
from html.parser import HTMLParser
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,tag,attrs):
  if tag in ['script','style']:self.skip+=1
  if tag in ['p','h1','h2','h3','h4','section']:self.parts.append('\n\n')
 def handle_endtag(self,tag):
  if tag in ['script','style']:self.skip=max(0,self.skip-1)
  if tag in ['p','h1','h2','h3','h4']:self.parts.append('\n\n')
 def handle_data(self,text):
  if not self.skip:self.parts.append(text)
def extract(raw):
 p=Extract();p.feed(raw.decode());return ''.join(p.parts)

B=Path(__file__).resolve().parents[1]/'packet';D=B/'private/primary';r=json.loads((D/'receipts.json').read_text())
jobs=[('haddad','https://arxiv.org/pdf/1904.10427v6','pdf')]
for k,u,kind in jobs:
 try:
  resp=urllib.request.urlopen(u,timeout=40);raw=resp.read();p=D/(k+'.'+kind);p.write_bytes(raw)
  if kind=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(D/(k+'.txt'))],check=True)
  else:
   tx=extract(raw);(D/(k+'.txt')).write_text(tx+'\n')
  tx=(D/(k+'.txt')).read_bytes();r.append({'id':k,'requested_url':u,'final_url':resp.url,'file':str(p.relative_to(B)),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'text_file':str((D/(k+'.txt')).relative_to(B)),'text_sha256':hashlib.sha256(tx).hexdigest(),'status':'success','semantic_read':False});print(k,len(raw),tx[:150])
 except Exception as e:r.append({'id':k,'requested_url':u,'status':'failed','error':str(e)});print(k,e)
(D/'receipts.json').write_text(json.dumps(r,indent=2)+'\n')
