import pathlib,json,hashlib
from bs4 import BeautifulSoup
D=pathlib.Path(__file__).parent;out=[]
for e in json.loads((D/'downloads.json').read_text()):
 if 'path' not in e:continue
 b=pathlib.Path(e['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256']
 t=BeautifulSoup(b,'html.parser').get_text(' ',strip=True);p=D/(e['name']+'.txt');p.write_text(t);out.append({'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
