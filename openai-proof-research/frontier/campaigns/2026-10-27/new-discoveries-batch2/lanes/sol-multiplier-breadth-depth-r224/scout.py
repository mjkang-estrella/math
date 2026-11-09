import sys
args=sys.argv[:];sys.argv=[sys.argv[0],'import']
import research as r,xml.etree.ElementTree as E,urllib.parse,json
sys.argv=args
ns={'a':'http://www.w3.org/2005/Atom'}
queries={
 'heat':'all:"heat content" AND all:conjecture',
 'smallball':'all:"small ball" AND all:conjecture',
 'persistence':'all:persistence AND all:conjecture AND cat:math.PR',
 'covariogram':'all:covariogram AND all:problem',
 'bernstein':'all:"Bernstein functions" AND all:conjecture',
 'fractional':'all:"fractional perimeter" AND all:conjecture',
 'torsion':'all:"torsional rigidity" AND all:conjecture',
 'transport':'all:"entropic transport" AND all:conjecture'}
if sys.argv[1]=='fetch':
 for name,q in queries.items():
  r.fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':6,'sortBy':'submittedDate','sortOrder':'descending'}),name+'-api.xml')
else:
 for p in (r.L/'retrieval').glob('*-api.xml'):
  if p.name not in [x+'-api.xml' for x in queries]:continue
  print('\nFILE',p.name)
  try:
   for e in E.parse(p).findall('a:entry',ns):
    print(e.findtext('a:id','',ns),e.findtext('a:published','',ns),e.findtext('a:title','',ns));print(e.findtext('a:summary','',ns)[:480])
  except Exception as e:print(e)
