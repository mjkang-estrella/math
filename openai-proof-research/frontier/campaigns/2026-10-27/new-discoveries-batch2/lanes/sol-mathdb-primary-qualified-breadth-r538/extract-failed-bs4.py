import pathlib,json,hashlib
from bs4 import BeautifulSoup
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'retrieval-bindings.json').read_text()):
 if 'failure' in e:continue
 p=P/(e['name']+'.html');b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for t in s(['script','style','annotation']):t.decompose()
 for t in s.find_all('math'):t.replace_with(t.get('alttext',t.get_text()))
 b=s.get_text('\n',strip=True).encode();p=P/(e['name']+'.txt');p.write_bytes(b);out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
