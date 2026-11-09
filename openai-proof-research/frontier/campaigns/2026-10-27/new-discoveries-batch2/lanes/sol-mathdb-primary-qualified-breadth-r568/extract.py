import json,pathlib,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.depth=0
 def handle_starttag(self,tag,attrs):
  if tag=="math":self.out.append(dict(attrs).get("alttext",""));self.depth+=1
 def handle_endtag(self,tag):
  if tag=="math":self.depth-=1
 def handle_data(self,data):
  if not self.depth:self.out.append(data)
D=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((D/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 b=(D/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());t=" ".join(" ".join(s.out).split());p=D/(e["path"]+".txt");p.write_text(t)
 out.append({'path':p.name,'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'derived_from':e['path']})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 t=(D/e['path']).read_text();print('\nSOURCE',e['path'])
 for word in ['Conjecture','conjecture','AGX','counterexample']:
  start=0;cnt=0
  while cnt<8:
   k=t.find(word,start)
   if k<0:break
   print(t[max(0,k-200):k+1800]);start=k+len(word);cnt+=1
