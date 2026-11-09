from retrieve import *
import xml.etree.ElementTree as E,urllib.parse
queries={
'wavelet-current':'all:"Bownik" AND (all:"Weber" OR all:"frame wavelet")',
'hh-current':'all:"Simic" AND (all:"Hermite-Hadamard" AND all:"best")',
'density-current':'all:"Niculescu" AND all:"positive series"',
'nets-current':'all:"geodesic multinets"',
'polling-current':'all:"gated" AND all:"1-limited"',
'tiling-current':'all:"tiling" AND au:Lev AND all:"density"',
'sheet-current':'au:Khoshnevisan AND all:"slices"',
'ramm-current':'au:Ramm AND all:"three open problems"'}
ns={'a':'http://www.w3.org/2005/Atom'}
for key,q in queries.items():
 d=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=8&sortBy=submittedDate&sortOrder=descending',key+'.xml')
 print('\nQUERY',key)
 if not d:continue
 for e in E.fromstring(d).findall('a:entry',ns):
  print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns));print(e.findtext('a:summary',namespaces=ns)[:1900])
for name,start,end in [('ramm',0,16000),('math_0510518v1',122000,135000)]:
 p=L/'primary'/(name+'.txt')
 if p.exists():
  h=hashlib.sha256(p.read_bytes()).hexdigest();(L/(name+'-text-freeze.json')).write_text(json.dumps({'path':str(p),'sha256':h}));print('BODY',name,p.read_text()[start:end]);assert hashlib.sha256(p.read_bytes()).hexdigest()==h
