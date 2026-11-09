import pathlib,json,hashlib
from bs4 import BeautifulSoup
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'download-bindings.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for t in s.find_all(['script','style','annotation']):t.decompose()
 text=s.get_text(' ',strip=True);n=e['path'].replace('.html','.txt');b=text.encode();(P/n).write_bytes(b);out.append({'path':n,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source':e['path']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 t=(P/e['path']).read_text();print('\nFILE',e['path'])
 import re
 for m in re.finditer(r'(?i)conjectur',t):print(t[max(0,m.start()-200):m.start()+1700])
