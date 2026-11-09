import json,pathlib,hashlib
from bs4 import BeautifulSoup
O=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((O/'downloads.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for m in s.find_all('math'):m.replace_with(m.get('alttext',m.get_text()))
 t=s.get_text(' ',strip=True);p=O/(e['name']+'.txt');p.write_text(t);b=p.read_bytes();out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(O/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
