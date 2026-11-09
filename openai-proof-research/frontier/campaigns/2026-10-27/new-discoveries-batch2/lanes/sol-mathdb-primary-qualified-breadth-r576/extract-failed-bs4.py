from pathlib import Path
import json,hashlib
from bs4 import BeautifulSoup
D=Path(__file__).resolve().parent;out=[]
for r in json.loads((D/'source-provenance.json').read_text()):
 if 'path' not in r:continue
 p=Path(r['path']);b=p.read_bytes();assert len(b)==r['size'] and hashlib.sha256(b).hexdigest()==r['sha256']
 s=BeautifulSoup(b,'html.parser')
 for m in s.find_all('math'):m.replace_with(m.get('alttext',m.get_text()))
 t=s.get_text(' ',strip=True);q=p.with_suffix('.txt');q.write_text(t)
 out.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),size=q.stat().st_size,source_sha256=r['sha256']))
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('bound derivatives',len(out))
