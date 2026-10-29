from pathlib import Path
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
def clean(b):
 p=Text();p.feed(b.decode());return " ".join(p.parts)
import json,re,hashlib
P=Path(__file__).resolve().parent; R=next(x for x in P.parents if x.name=='openai-proof-research')
for f in (P/'sources').glob('*.html'):
 s=clean(f.read_bytes());f.with_suffix('.txt').write_text(s)
 for m in re.finditer(r'(?i)conjecture|question|problem',s):
  print(f.name,s[max(0,m.start()-150):m.end()+650])
terms=re.compile(r'quasi.regulariz|Hoang|Mandrescu|Pereyra|domination.polynomial|Alikhani|AutoGraphForge|Pastorek',re.I);files=[];hits=[]
for f in R.rglob('*'):
 if not f.is_file() or P in f.parents:continue
 if f.suffix.lower() not in ['.md','.txt','.json'] or not any(x in f.name.lower() for x in ['summary','discovery','findings','proof','review','ledger']):continue
 b=f.read_bytes();files.append(dict(path=str(f.relative_to(R)),sha256=hashlib.sha256(b).hexdigest()))
 for i,l in enumerate(b.decode(errors='replace').splitlines(),1):
  if terms.search(l):hits.append(dict(path=str(f.relative_to(R)),line=i,text=l[:2500]))
(P/'duplicate-audit.json').write_text(json.dumps(dict(terms=terms.pattern,files=files,hits=hits),indent=2));print('DUPLICATES',len(files),json.dumps(hits))
