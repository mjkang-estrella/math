import pathlib,json,hashlib
from bs4 import BeautifulSoup
D=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((D/'retrieval-bindings.json').read_text()):
 if 'path' not in e:continue
 b=(D/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 soup=BeautifulSoup(b,'html.parser')
 for node in soup.select('annotation'):node.decompose()
 s=soup.get_text(' ',strip=True);p=D/e['path'].replace('.html','.txt');p.write_text(s)
 out.append({'path':p.name,'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'parent_sha256':e['sha256']})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 s=(D/e['path']).read_text();print('\nSOURCE',e['path'])
 import re
 for m in re.finditer(r'(?i)conjecture',s):print(s[max(0,m.start()-250):m.start()+1800])
