import pathlib,json,hashlib
from bs4 import BeautifulSoup
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for m in s.find_all('math'):m.replace_with(' $'+m.get('alttext',m.get_text())+'$ ')
 p=p.with_suffix('.txt');b=s.get_text(' ',strip=True).encode();p.write_bytes(b);out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source':e['url'],'derivation':'BeautifulSoup math alttext replacement then get_text space strip'})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
