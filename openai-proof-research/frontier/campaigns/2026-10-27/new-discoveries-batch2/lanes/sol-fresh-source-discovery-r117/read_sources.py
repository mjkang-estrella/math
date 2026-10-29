import json,hashlib,re
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent;B=L.parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
for name in ['inverse-z.html','psw.html','aluffi-proof.html','qrook.html']:
 p=L/'sources'/name;t=Text();t.feed(p.read_text());s=' '.join(t.parts);s=re.sub(r'\s+',' ',s)
 print(name)
 for term in ['Conjecture 1.5','Theorem 1.1','Conjecture 7.8','Proposition 1','Proposition 2','Theorem 1.6']:
  m=re.search(re.escape(term),s)
  if m:print(term,s[max(0,m.start()-80):m.end()+1100])
 (L/'sources'/(name+'.txt')).write_text(s)
for p in [B/'sol-renyi-registry-gap-closure-r3/intervals.json',B/'sol-renyi-registry-gap-closure-r3/exactcoverage.json']:
 d=json.loads(p.read_text());print(p.name, 'keys',list(d[0]) if isinstance(d,list) else list(d))
 if isinstance(d,list):
  for x in d:print({k:v for k,v in x.items() if k not in ['commits','files','patches']})
 print('end')
frozen=json.loads((L/'frozen-before.json').read_text())
for p in [B/'sol-fresh-source-discovery-r92/discovery.md',B/'sol-fresh-source-discovery-r59/discovery.md',B/'sol-fresh-source-discovery-r105/sources/literal-6.txt',B/'sol-fresh-source-discovery-r105/sources/literal-7.txt']:
 frozen.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(L/'frozen-before.json').write_text(json.dumps(frozen,indent=2))
with (L/'sourcehashes-before.json').open('w') as f:json.dump({str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (L/'sources').iterdir() if p.is_file()},f,indent=2)
