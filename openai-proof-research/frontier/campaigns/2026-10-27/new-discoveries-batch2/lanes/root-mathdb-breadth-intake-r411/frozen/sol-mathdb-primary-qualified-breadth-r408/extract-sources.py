import pathlib,json,hashlib,subprocess
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,s):self.parts.append(s)
for r in json.loads((L/'source-provenance.json').read_text()):
 if 'path' not in r:continue
 p=L/r['path']; b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']
 if p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 else:
  a=Parser();a.feed(b.decode('utf-8','replace'));p.with_suffix('.txt').write_text('\n'.join(s.strip() for s in a.parts if s.strip()))
