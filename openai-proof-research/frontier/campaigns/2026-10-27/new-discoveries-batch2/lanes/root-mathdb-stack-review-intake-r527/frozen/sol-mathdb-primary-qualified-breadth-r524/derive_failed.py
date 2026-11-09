from pathlib import Path
import json,hashlib
from bs4 import BeautifulSoup
O=Path(__file__).resolve().parent;out=[]
for e in json.loads((O/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 soup=BeautifulSoup(b,'html.parser')
 for el in soup.find_all('math'):el.replace_with(el.get('alttext',el.get_text()))
 p=p.with_suffix('.txt');p.write_text(soup.get_text('\n',strip=True));b=p.read_bytes();out.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest(),source=e['url']))
(O/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
