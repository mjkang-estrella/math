import pathlib,sys,runpy,urllib.parse,xml.etree.ElementTree as E
L=pathlib.Path(__file__).resolve().parent
queries={
'braid':'all:"braid group commutator"',
'biane':'all:"Biane" AND all:"trees"',
'pisot':'ti:"Pisot" AND (abs:"conjugates" OR abs:"Hare")',
'sobolev':'all:"extremal Sobolev"',
'shuffle':'all:"random-to-random" AND all:"posets"',
'lattice':'ti:"lattice games"',
'semigroup':'ti:"number of numerical semigroups"',
'hecke':'all:"Hecke" AND all:"Ramanujan" AND au:"Ashok"'}
for key in sys.argv[1:]:
 url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=queries[key],max_results=12,sortBy='submittedDate',sortOrder='descending'))
 sys.argv=['run.py','fetch',key+'.atom',url];runpy.run_path(str(L/'run.py'),run_name='__main__')
 p=L/'primary'/(key+'.atom')
 if p.exists():
  root=E.fromstring(p.read_bytes());n={'a':'http://www.w3.org/2005/Atom'}
  for e in root.findall('a:entry',n):print(key,*(e.findtext('a:'+s,default='',namespaces=n).strip().replace('\n',' ') for s in ['id','title','published','summary']))
