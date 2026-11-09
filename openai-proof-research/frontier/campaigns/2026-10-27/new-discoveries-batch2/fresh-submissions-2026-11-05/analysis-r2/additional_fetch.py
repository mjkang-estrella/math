from pathlib import Path
import requests,hashlib,json,datetime,subprocess,re
from html.parser import HTMLParser
p=Path(__file__).parent;receipts=[]
class Text(HTMLParser):
 def __init__(self):super().__init__();self.bits=[]
 def handle_data(self,t):self.bits.append(t)
items=[('gamma-resolution.pdf','https://arxiv.org/pdf/2609.20212v1'),('dlmf-10-21.html','https://dlmf.nist.gov/10.21'),('omega-current.html','https://www.trureturing.org/conjectures'),('openai-current.html','https://github.com/openai/math')]
for name,url in items:
 r=requests.get(url,timeout=45);(p/'sources'/name).write_bytes(r.content);receipts.append({'url':url,'status':r.status_code,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(r.content).hexdigest(),'path':'sources/'+name})
 if r.status_code==200:
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))])
  else:
   h=Text();h.feed(r.text);t='\n'.join(h.bits);(p/'sources'/name.replace('.html','.txt')).write_text(t)
(p/'additional-source-receipts.json').write_text(json.dumps(receipts,indent=2));print(receipts)
