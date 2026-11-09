import pathlib,json,hashlib,urllib.request,datetime
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent;L=P.parent
refs=json.loads((P/'flat-bindings.json').read_text())
def bind(p):
 b=p.read_bytes();e={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)};refs.append(e);return e
for f in (L/'sol-mathdb-primary-qualified-breadth-r454').rglob('*'):
 if f.is_file() and (f.name.startswith('14298804') or f.name in ['provenance.json','source-provenance.json','manifest.json']):bind(f)
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
pro=[]
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,s):self.out.append(s)
for ident in ['11695867','14298801']:
 url='https://ems.press/journals/owr/articles/'+ident
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research statement fidelity check'}),timeout=25) as r:b=r.read()
  f=P/(ident+'.html');f.write_bytes(b);e=bind(f)
  # Bytes bound before parsing; derivative bound before any content display.
  parser=Parser();parser.feed(b.decode());t=P/(ident+'.txt');t.write_text('\n'.join(parser.out));te=bind(t)
  pro.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw':e,'derivative':te,'coverage':'HTML only; no PDF body or proof audit'})
 except Exception as e:pro.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'failure':str(e),'retry':False})
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n');(P/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n');print(json.dumps(pro,indent=2))
