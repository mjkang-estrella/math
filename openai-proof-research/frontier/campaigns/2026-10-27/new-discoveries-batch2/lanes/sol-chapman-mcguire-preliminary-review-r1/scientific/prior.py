from retrieve import *
import urllib.parse,xml.etree.ElementTree as E
qs=['all:"Nullities for a class"','all:"Toeplitz" AND all:"payoff"','all:"Roman" AND all:"supercritical"','all:"split overlaps"','all:"twisted trace"','all:"fixed row sums"','all:"pressing" AND all:"finite field"']
for i,q in enumerate(qs):
 p=fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':15,'sortBy':'submittedDate','sortOrder':'descending'}),'prior-'+str(i)+'.xml')
 if p:
  ns={'a':'http://www.w3.org/2005/Atom'};r=E.fromstring(p.read_bytes());print('QUERY',q)
  for e in r.findall('a:entry',ns):print(' '.join(e.findtext('a:'+k,default='',namespaces=ns).split()) for k in []) if False else print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns)[:1400])
