from retrieve import fetch,L
import urllib.parse,xml.etree.ElementTree as E
queries=[('questions','cat:math.CO AND ti:questions AND submittedDate:[200001010000 TO 201712312359]'),('conjectures','cat:math.CO AND ti:conjectures AND submittedDate:[200001010000 TO 201712312359]')]
for name,q in queries:
 fetch(name+'.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,max_results=30,sortBy='submittedDate',sortOrder='descending')))
 root=E.parse(L/'primary'/(name+'.xml'));ns={'a':'http://www.w3.org/2005/Atom'}
 for e in root.findall('a:entry',ns): print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
