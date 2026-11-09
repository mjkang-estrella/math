import pathlib,json,hashlib
from bs4 import BeautifulSoup
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'downloads.json').read_text()):
 if 'path' not in e:continue
 b=pathlib.Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for m in s.find_all('math'):m.replace_with(m.get('alttext',m.get_text()))
 for n in s(['script','style']):n.decompose()
 t=s.get_text(' ',strip=True);p=P/(e['name']+'.txt');p.write_text(t);bb=p.read_bytes();out.append({'path':str(p),'size':len(bb),'sha256':hashlib.sha256(bb).hexdigest(),'parent_sha256':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 t=pathlib.Path(e['path']).read_text();print('\nSOURCE',e['path'])
 import re
 for m in re.finditer('conjectur|odd|j13',t,re.I):
  if 'korselt' in e['path'] and not re.search('conjectur|odd',m.group(),re.I):continue
  print(t[max(0,m.start()-450):m.end()+1400])
