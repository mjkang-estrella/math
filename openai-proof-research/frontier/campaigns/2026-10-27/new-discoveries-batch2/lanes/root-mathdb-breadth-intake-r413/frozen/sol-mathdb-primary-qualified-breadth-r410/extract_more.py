from pathlib import Path
import json,subprocess,hashlib,re
from html.parser import HTMLParser
L=Path(__file__).parent;P=L/'primary'
class T(HTMLParser):
 def __init__(self):super().__init__();self.s=[]
 def handle_data(self,d):self.s.append(d)
refs=[]
for m in sorted(P.glob('*.meta.json')):
 d=json.loads(m.read_text())
 if 'file' not in d:continue
 f=P/d['file'];b=f.read_bytes();assert hashlib.sha256(b).hexdigest()==d['sha256']
 out=f.with_suffix('.txt')
 if f.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(f),str(out)],check=True)
 else:
  t=T();t.feed(b.decode('utf-8',errors='replace'));out.write_text('\n'.join(t.s))
 refs.append({'source':f.name,'source_sha256':d['sha256'],'text':out.name,'text_sha256':hashlib.sha256(out.read_bytes()).hexdigest()})
(P/'extractions.json').write_text(json.dumps(refs,indent=2)+'\n')
