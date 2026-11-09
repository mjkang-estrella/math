import urllib.parse,xml.etree.ElementTree as E,json
from retrieve import fetch,L
queries=[('nt2016','cat:math.NT AND abs:"we conjecture" AND submittedDate:[201601010000 TO 201612312359]'),('ra2023','cat:math.RA AND abs:conjecture AND submittedDate:[202301010000 TO 202312312359]'),('co2024','cat:math.CO AND abs:"we conjecture" AND submittedDate:[202401010000 TO 202412312359]')]
for label,q in queries:
 fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=6,sortBy='submittedDate',sortOrder='ascending')),label+'.xml')
ns={'a':'http://www.w3.org/2005/Atom'};entries=[]
for p in (L/'sources').glob('*.xml'):
 for e in E.parse(p).findall('a:entry',ns):
  r={k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','summary','published','updated']};r['authors']=[a.text for a in e.findall('a:author/a:name',ns)];entries.append(r)
(L/'entries.json').write_text(json.dumps(entries,indent=2))
for r in entries:print(r['id'],r['title'],r['authors'],r['summary'])
