from retrieve import fetch,L
import urllib.parse,xml.etree.ElementTree as E
from concurrent.futures import ThreadPoolExecutor
qs={'kim':'au:Kim AND all:hypersimplices','boggle-refined':'ti:Boggle AND cat:math.CO','hadamard-refined':'ti:Hadamard AND all:regularity','rectangular-refined':'ti:"rectangular Catalan"','twenty-refined':'ti:"Twenty" AND au:Filmus','brain-refined':'ti:"Graph Brain"'}
def get(k):
 fetch(k+'.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=qs[k],max_results=8,sortBy='submittedDate',sortOrder='descending')))
 root=E.parse(L/'primary'/(k+'.xml'));ns={'a':'http://www.w3.org/2005/Atom'}
 print(k,[(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns)[:600]) for e in root.findall('a:entry',ns)],flush=True)
with ThreadPoolExecutor(max_workers=3) as ex:list(ex.map(get,qs))
