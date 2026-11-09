from retrieve import *
import urllib.parse,xml.etree.ElementTree as E
q=sys.argv[1]
d=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&start=0&max_results=35&sortBy=relevance',sys.argv[2]+'.xml')
ns={'a':'http://www.w3.org/2005/Atom'}
for e in E.fromstring(d).findall('a:entry',ns):
 print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:published',namespaces=ns));print(e.findtext('a:summary',namespaces=ns))
