import pathlib,json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d) 
P=pathlib.Path(__file__).resolve().parent
out=[]
for e in json.loads((P/'downloads.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode())
 p=P/e['path'].replace('.html','.txt');p.write_text(' '.join(s.parts).replace(' .','.'),encoding='utf8');b=p.read_bytes();out.append({'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for name,words in [('commutative',['conjecture','K n','K_n']),('fishburn',['Conjecture','1324,2143','3214']),('young',['Conjecture','14,3'])]:
 text=(P/(name+'.txt')).read_text();print('\nSOURCE',name,'HEADER',text[:500])
 import re
 for m in re.finditer('conjectur',text,re.I):print(text[max(0,m.start()-300):m.start()+850])
