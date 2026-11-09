from explore import *
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urlencode
queries={'schur':'all:"monochromatic" AND (all:"Koutschan" OR all:"generalized Schur")','cores':'all:"self-conjugate" AND all:"generalized Dyck"','nut':'all:"regular nut graphs"','code':'all:"perfect code" AND (all:"subgroup" OR all:"code-perfect")','pattern':'all:"inversion sequences" AND all:"Wilf"'}
def one(kv):
 k,q=kv;p=L/(k+'-prior.xml');url='https://export.arxiv.org/api/query?'+urlencode(dict(search_query=q,max_results=35,sortBy='lastUpdatedDate',sortOrder='descending'))
 if not fetch(url,p):return
 ns={'a':'http://www.w3.org/2005/Atom'};out=[]
 for e in E.parse(p).findall('a:entry',ns):
  d={k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','summary','published','updated']};out.append(d)
 (L/(k+'-prior.json')).write_text(json.dumps(out,indent=2))
 print(k,[(d['id'],d['title'],d['summary'][:700]) for d in out])
with ThreadPoolExecutor(max_workers=3) as ex:list(ex.map(one,queries.items()))
# Bind established history index in place, without copying its old evidence tree.
p=B/'lanes/sol-wide-finite-source-scout-r256/history-index.txt';before=digest(p);s=p.read_text();assert before==digest(p)
terms=['Koutschan','Schur triples','code-perfect','generalized quaternion','irredundance','Solov','Fishel','Gekhtman','generalized Dyck']
out={'path':str(p),'sha256':before,'hits':{t:[s[max(0,i-120):i+300] for i in [s.lower().find(t.lower())] if i>=0] for t in terms}}
(L/'semantic-history.json').write_text(json.dumps(out,indent=2));print('SEMANTIC',out)
