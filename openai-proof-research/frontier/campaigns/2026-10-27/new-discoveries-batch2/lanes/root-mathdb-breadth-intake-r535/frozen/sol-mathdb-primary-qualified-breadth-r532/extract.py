from pathlib import Path
import json,hashlib
from bs4 import BeautifulSoup
D=Path(__file__).resolve().parent;a=[]
for e in json.loads((D/'source-download-bindings.json').read_text()):
 if 'path' not in e:continue
 p=Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for t in s.find_all('math'):t.replace_with(' $'+t.get('alttext','[MISSING MATH]')+'$ ')
 for t in s(['script','style']):t.decompose()
 p=p.with_suffix('.txt');b=s.get_text(' ',strip=True).encode();p.write_bytes(b);a.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'derivative-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
