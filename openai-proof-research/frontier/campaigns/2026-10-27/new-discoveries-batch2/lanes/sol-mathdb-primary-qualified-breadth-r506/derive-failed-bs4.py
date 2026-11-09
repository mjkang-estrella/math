from pathlib import Path
from bs4 import BeautifulSoup
import json,hashlib
O=Path(__file__).parent;log=[]
for e in json.loads((O/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=Path(e['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e['size']
 s=BeautifulSoup(b,'html.parser');v=s.find('article');v=v or s
 for m in v.find_all('math'):
  m.replace_with(m.get('alttext') or m.get_text())
 t=v.get_text(' ',strip=True);p=p.with_suffix('.txt');p.write_text(t+'\n');b=p.read_bytes();log.append({'path':str(p.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'derives_from':e['sha256']})
(O/'derivative-bindings.json').write_text(json.dumps(log,indent=2)+'\n')
