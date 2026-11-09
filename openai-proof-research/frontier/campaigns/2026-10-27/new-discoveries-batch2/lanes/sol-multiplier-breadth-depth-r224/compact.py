import pathlib,json,xml.etree.ElementTree as E
L=pathlib.Path(__file__).resolve().parent
a=json.loads((L/'alias-results.json').read_text())
for term in ['2608.17927','2609.11418','2609.28707','2502.02989','2608.02288','2502.13819','2608.11686','2609.23051']:
 hits=[h for h in a['hits'] if any(m['term']==term for m in h['matches'])]
 print(term,'hits',len(hits))
 for h in hits[:5]:print(h['path'],next(m['context'] for m in h['matches'] if m['term']==term)[:550])
ns={'a':'http://www.w3.org/2005/Atom'}
for name in ['survivors-api.xml','citing-api.xml']:
 print(name)
 for e in E.parse(L/'retrieval'/name).findall('a:entry',ns):
  title=e.findtext('a:title','',ns)
  if name=='citing-api.xml' and 'Bessel' not in title and 'Multiplier' not in title and 'multiplier' not in title:continue
  print(e.findtext('a:id','',ns),title)
