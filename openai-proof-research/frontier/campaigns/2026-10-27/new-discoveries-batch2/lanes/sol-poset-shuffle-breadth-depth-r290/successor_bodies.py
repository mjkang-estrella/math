from research import *
import xml.etree.ElementTree as E
ns={'a':'http://www.w3.org/2005/Atom'}
for key in ['delta-proof','infinite-log']:
 for e in E.parse(L/'primary'/(key+'.atom')).findall('a:entry',ns):print(key,e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
fetch('hotspots.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"hot spots" AND au:Werner')+'&max_results=5')
for id in ['1509.08580v3','2503.17580v4']:
 fetch(id+'.pdf','https://arxiv.org/pdf/'+id)
 if (L/'primary'/(id+'.pdf')).exists():extract(L/'primary'/(id+'.pdf'))
