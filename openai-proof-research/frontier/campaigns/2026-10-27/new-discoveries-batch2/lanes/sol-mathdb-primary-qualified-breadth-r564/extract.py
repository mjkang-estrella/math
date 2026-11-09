import pathlib,json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0
 def handle_starttag(self,tag,attrs):
  if tag=="math":self.out.append(dict(attrs).get("alttext",""));self.math+=1
  elif tag in ("p","div","section"):self.out.append("\n")
 def handle_endtag(self,tag):
  if tag=="math":self.math-=1
 def handle_data(self,data):
  if not self.math:self.out.append(data)
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'downloads.json').read_text()):
 if 'path' not in e:continue
 b=pathlib.Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());t=" ".join(" ".join(s.out).split());p=P/(e["name"]+".txt");p.write_text(t);bb=p.read_bytes();out.append({"path":str(p),"size":len(bb),"sha256":hashlib.sha256(bb).hexdigest(),"parent_sha256":e["sha256"]})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 t=pathlib.Path(e['path']).read_text();print('\nSOURCE',e['path'])
 import re
 for m in re.finditer('conjectur|odd|j13',t,re.I):
  if 'korselt' in e['path'] and not re.search('conjectur|odd',m.group(),re.I):continue
  print(t[max(0,m.start()-450):m.end()+1400])
