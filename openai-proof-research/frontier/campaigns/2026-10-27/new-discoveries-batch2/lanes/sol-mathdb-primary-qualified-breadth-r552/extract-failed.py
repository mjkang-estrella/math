import pathlib,json,hashlib
from bs4 import BeautifulSoup
P=pathlib.Path(__file__).resolve().parent
out=[]
for e in json.loads((P/'downloads.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=BeautifulSoup(b,'html.parser')
 for t in s(['script','style']):t.decompose()
 p=P/e['path'].replace('.html','.txt');p.write_text(s.get_text(' ',strip=True).replace(' .','.'),encoding='utf8');b=p.read_bytes();out.append({'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for name,words in [('commutative',['conjecture','K n','K_n']),('fishburn',['Conjecture','1324,2143','3214']),('young',['Conjecture','14,3'])]:
 text=(P/(name+'.txt')).read_text();print('\nSOURCE',name,'HEADER',text[:500])
 import re
 for m in re.finditer('conjectur',text,re.I):print(text[max(0,m.start()-300):m.start()+850])
