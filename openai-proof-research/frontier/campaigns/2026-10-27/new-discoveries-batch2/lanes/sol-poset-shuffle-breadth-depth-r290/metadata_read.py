from research import *
import xml.etree.ElementTree as E,re
ns={'a':'http://www.w3.org/2005/Atom'}
for p in sorted((L/'primary').glob('*.atom')):
 if p.stem.startswith('shuffle'):continue
 print(p.name)
 for e in E.parse(p).findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
html=(L/'primary'/'shuffle-bing.html').read_text()
print('BING',re.sub('<[^>]*>',' ',html)[-24000:])
