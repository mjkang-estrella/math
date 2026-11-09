import json,pathlib,hashlib
from bs4 import BeautifulSoup
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for m in s.find_all('math'):
  m.replace_with(m.get('alttext',m.get_text(' ',strip=True)))
 for a in s(['script','style']):a.decompose()
 text=s.get_text('\n',strip=True);q=p.with_suffix('.txt');q.write_text(text);bb=q.read_bytes();out.append(dict(path=str(q),size=len(bb),sha256=hashlib.sha256(bb).hexdigest(),derived_from=e['sha256']))
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
