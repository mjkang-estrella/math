from retrieve import fetch,L
import urllib.parse,xml.etree.ElementTree as E,hashlib,json,re
from concurrent.futures import ThreadPoolExecutor
queries={'boggle':'all:"Boggle"','divisibility':'all:"Tripathy" AND all:"divisibility"','hill':'all:"Hill operators" AND all:"combinatorial"','ehrhart':'all:"hypersimplices" AND all:"Early"','hadamard':'all:"regular" AND all:"Hadamard"','rectangular':'all:"rectangular" AND all:"Schur"','twenty':'ti:"Twenty" AND ti:"questions"','brain':'all:"girth" AND all:"theta" AND all:"independence"'}
def get(k):
 fetch(k+'-status.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=queries[k],max_results=5,sortBy='submittedDate',sortOrder='descending')))
 root=E.parse(L/'primary'/(k+'-status.xml'));ns={'a':'http://www.w3.org/2005/Atom'}
 return k,[dict(id=e.findtext('a:id',namespaces=ns),title=e.findtext('a:title',namespaces=ns),published=e.findtext('a:published',namespaces=ns),summary=e.findtext('a:summary',namespaces=ns)) for e in root.findall('a:entry',ns)]
with ThreadPoolExecutor(max_workers=3) as ex: results=dict(ex.map(get,queries))
(L/'current-status.json').write_text(json.dumps(results,indent=2))
aliases={'boggle':'boggle|needleman','divisibility':'tripathy|kostka','hill':'djakov|mityagin|hill operator','ehrhart':'hypersimplic|decorated ordered','hadamard':'hadamard|banica|pittau','rectangular':'rectangular catalan|bergeron|shuffle','twenty':'twenty.*questions|dyadic distribution|uopt','brain':'graph brain|lov.sz theta'}
paths=sorted(p for d in L.parent.iterdir() if d.is_dir() and d!=L for p in d.iterdir() if p.name in ['discovery.md','SUMMARY.md','SCOUTING.md','FAILURES.md'] and p.stat().st_size<200000)
bindings=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths]
(L/'history-bindings.json').write_text(json.dumps(bindings,indent=2))
hits={k:[] for k in aliases}
for p,b in zip(paths,bindings):
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==b['sha256'];s=data.decode(errors='replace')
 for k,a in aliases.items():
  lines=[x[:400] for x in s.splitlines() if re.search(a,x,re.I)]
  if lines:hits[k].append(dict(path=str(p),lines=lines[:3]))
(L/'history-hits.json').write_text(json.dumps(hits,indent=2))
print('HISTORY',len(paths),{k:len(v) for k,v in hits.items()})
for k,v in results.items():
 print(k)
 for r in v: print(r['id'],r['title'],r['summary'][:550])
