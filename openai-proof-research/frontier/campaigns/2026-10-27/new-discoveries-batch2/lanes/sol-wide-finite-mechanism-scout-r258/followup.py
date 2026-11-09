from retrieve import *
import urllib.parse,xml.etree.ElementTree as E
for i,q in enumerate(['ti:"Twisted Trace" AND au:McGuire','au:McGuire AND all:Fibonacci','ti:"Roman Domination" AND all:supercritical','ti:"Split Overlaps"','ti:"Toeplitz" AND au:Evans']):
 p=fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':25,'sortBy':'submittedDate','sortOrder':'descending'}),'followup-'+str(i)+'.xml')
 if p:
  ns={'a':'http://www.w3.org/2005/Atom'};r=E.fromstring(p.read_bytes());print(q)
  for e in r.findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),' '.join(e.findtext('a:summary',default='',namespaces=ns).split())[:1200])
p=fetch('https://api.openalex.org/works?'+urllib.parse.urlencode({'search':'On a Family of Twisted Trace Curves over Finite Fields','per-page':5}),'openalex-trace.json')
if p:
 j=json.loads(p.read_bytes())
 for x in j.get('results',[]):print(x['id'],x['title'],x.get('doi'),x.get('cited_by_count'),x.get('cited_by_api_url'))
