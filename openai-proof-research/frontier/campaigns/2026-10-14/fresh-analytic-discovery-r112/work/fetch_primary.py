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
jobs=[('lawler-sheffield-pdf','https://arxiv.org/pdf/0906.3804v2','pdf'),('han-monotonicity','https://arxiv.org/pdf/1710.07953v2','pdf'),('campbell-smoothing','https://arxiv.org/html/2507.02854v1','html')]
for k,u,kind in jobs:
 try:
  resp=urllib.request.urlopen(u,timeout=40);raw=resp.read();p=D/(k+'.'+kind);p.write_bytes(raw)
  if kind=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(D/(k+'.txt'))],check=True)
  else:
   tx=extract(raw);(D/(k+'.txt')).write_text(tx+'\n')
  tx=(D/(k+'.txt')).read_bytes();r.append({'id':k,'requested_url':u,'final_url':resp.url,'file':str(p.relative_to(B)),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'text_file':str((D/(k+'.txt')).relative_to(B)),'text_sha256':hashlib.sha256(tx).hexdigest(),'status':'success','semantic_read':False});print(k,len(raw),tx[:150])
 except Exception as e:r.append({'id':k,'requested_url':u,'status':'failed','error':str(e)});print(k,e)
p=D/'pratelli-bisobolev.html';tx=extract(p.read_bytes());(D/'pratelli-readable.txt').write_text(tx)
r.append({'id':'pratelli-readable','derived_from':'private/primary/pratelli-bisobolev.html','file':'private/primary/pratelli-readable.txt','sha256':hashlib.sha256(tx.encode()).hexdigest(),'bytes':len(tx.encode()),'status':'derived','semantic_read':False})
(D/'receipts.json').write_text(json.dumps(r,indent=2)+'\n')
