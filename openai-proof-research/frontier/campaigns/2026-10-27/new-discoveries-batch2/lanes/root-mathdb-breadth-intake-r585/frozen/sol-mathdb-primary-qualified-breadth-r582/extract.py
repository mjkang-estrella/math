from pathlib import Path
import json,hashlib,subprocess,re
D=Path(__file__).parent;out=[]
for x in json.loads((D/'source-provenance.json').read_text()):
 if 'sha256' not in x:continue
 p=D/x['file'];b=p.read_bytes();assert len(b)==x['size'] and hashlib.sha256(b).hexdigest()==x['sha256']
 t=p.with_suffix('.txt') if p.suffix=='.pdf' else p.with_suffix('.html.txt')
 if p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
 else:
  from html.parser import HTMLParser
  class P(HTMLParser):
   def handle_data(self,d):self.a.append(d)
  h=P();h.a=[];h.feed(b.decode());t.write_text('\n'.join(h.a))
 b=t.read_bytes();out.append({'file':t.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent':x['file']})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
