import pathlib, hashlib, json, shutil, sys, os, datetime
import urllib.request, urllib.parse, xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(paths,folder):
 out=[]; d=L/folder; d.mkdir(exist_ok=True)
 for i,p in enumerate(paths):
  p=pathlib.Path(p); h=sha(p); q=d/(str(i)+'-'+p.name); shutil.copyfile(p,q)
  assert h==sha(q)==sha(p)
  out.append(dict(original=str(p),copy=str(q),sha256=h))
 (L/(folder+'-freeze.json')).write_text(json.dumps(out,indent=2)); return out
if sys.argv[1]=='init':
 a=freeze([B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md'],'administrative')
 for x in a:
  t=pathlib.Path(x['copy']).read_text(); j=None
  if x['original'].endswith('.json'):
   j=json.loads(t); print(pathlib.Path(x['original']).name, list(j) if isinstance(j,dict) else len(j))
 print('RECENT')
 for n in ['sol-wide-analytic-scout-r223','sol-wide-analysis-scout-r221','sol-wide-new-analysis-r227','sol-truncated-cosine-breadth-depth-r244','sol-subsum-multiplicity-breadth-depth-r239']:
  p=B/'lanes'/n/'SUMMARY.md'
  if p.exists(): print(n,p.read_text()[:5000])
 print('GASULL PATHS')
 p=B/'lanes/sol-wide-new-analysis-r227/primary'
 for q in p.iterdir():print(q.name,q.stat().st_size)
if sys.argv[1]=='search':
 d=L/'sources'; d.mkdir(exist_ok=True)
 queries=['all:"discrete renewal sequences"','all:"unfair" AND all:"polynomials"','all:"Seneta" AND all:"Williamson"','all:"convergence rate" AND all:"harmonic"']
 for k,query in enumerate(queries):
  u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=query,start=0,max_results=35,sortBy='submittedDate',sortOrder='descending'))
  try:
   data=urllib.request.urlopen(u,timeout=25).read(2000000); p=d/('current'+str(k)+'.xml');p.write_bytes(data)
   freeze([p],'current'+str(k)+'-frozen')
   root=ET.fromstring(data); ns={'a':'http://www.w3.org/2005/Atom'}
   for e in root.findall('a:entry',ns): print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
  except Exception as e: print(type(e).__name__,str(e)); (L/('search-failure'+str(k)+'.txt')).write_text(str(e))
if sys.argv[1]=='fetch':
 ids=sys.argv[2:]; d=L/'sources';d.mkdir(exist_ok=True)
 hist=[]
 for p in B.glob('lanes/*/SCOUTING.md'):
  if p.parent==L:continue
  h=sha(p); t=p.read_text(errors='replace'); assert h==sha(p)
  matches=[a for a in ids if a.split('v')[0] in t]
  if matches:print('HISTORY',str(p),matches)
  hist.append(dict(path=str(p),sha256=h,matches=matches))
 (L/'history-index.json').write_text(json.dumps(hist,indent=2))
 for a in ids:
  p=d/(a+'.pdf'); u='https://arxiv.org/pdf/'+a
  try:
   data=urllib.request.urlopen(u,timeout=25).read(6000000);p.write_bytes(data)
   if not data.startswith(b'%PDF'):raise ValueError('not PDF')
   freeze([p],a+'-frozen')
   import subprocess
   subprocess.run(['pdftotext','-layout',str(p),str(d/(a+'.txt'))],check=True)
   freeze([d/(a+'.txt')],a+'-text-frozen')
   print('FETCHED',a,len(data))
  except Exception as e:
   print('FAIL',a,str(e));(L/(a+'-failure.txt')).write_text(u+'\n'+str(e))
if sys.argv[1]=='read':
 for a in sys.argv[2:]:
  p=L/'sources'/(a+'.txt');h=sha(p); t=p.read_text();print('\nSOURCE',a,'\n',t[:100000]);assert h==sha(p)
if sys.argv[1]=='extract':
 import re
 a=sys.argv[2];p=L/'sources'/(a+'.txt');h=sha(p);t=p.read_text()
 for m in re.finditer(r'(?im)^.*(?:Problem \d|Conjecture \d|Question \d|Contents|Abstract).*$',t):print(t[max(0,m.start()-150):m.end()+1800])
 assert h==sha(p)
if sys.argv[1]=='pages':
 a=sys.argv[2];p=L/'sources'/(a+'.txt');h=sha(p);t=p.read_text();pages=t.split('\f')
 for i in range(int(sys.argv[3])-1,min(int(sys.argv[4]),len(pages))):print('PAGE',i+1,pages[i])
 assert sha(p)==h
if sys.argv[1]=='context':
 p=L/'sources'/(sys.argv[2]+'.txt');h=sha(p);t=p.read_text();term=sys.argv[3]
 import re
 for m in list(re.finditer(re.escape(term),t,re.I))[:15]:print(t[max(0,m.start()-400):m.end()+900])
 assert sha(p)==h
if sys.argv[1]=='prior':
 queries=['au:Savov AND all:renewal','all:renewal AND all:maximal AND all:polynomial']
 for k,q in enumerate(queries):
  u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=25,sortBy='submittedDate',sortOrder='descending'))
  p=L/'sources'/('prior'+str(k)+'.xml')
  try:
   p.write_bytes(urllib.request.urlopen(u,timeout=25).read(1000000));freeze([p],'prior'+str(k)+'-frozen')
   r=ET.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
   for e in r.findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:published',namespaces=ns),e.findtext('a:updated',namespaces=ns))
  except Exception as e:(L/('prior'+str(k)+'-failure.txt')).write_text(str(e));print(str(e))
if sys.argv[1]=='reconcile':
 rows=[]
 for n in ['sol-wide-new-analysis-r227','sol-wide-analytic-scout-r223','sol-wide-analysis-scout-r221','sol-truncated-cosine-breadth-depth-r244','sol-subsum-multiplicity-breadth-depth-r239']:
  p=B/'lanes'/n/'SUMMARY.md';h=sha(p);t=p.read_text();assert sha(p)==h
  rows.append({'path':str(p),'sha256':h,'excerpt':t[:6000]})
 (L/'recent-summary-reference-recheck.json').write_text(json.dumps(rows,indent=2));print('Rechecked',len(rows),'immutable summary references')
if sys.argv[1]=='aliases':
 terms=sys.argv[2:];out=[]
 for p in (p for n in ['SCOUTING.md','SUMMARY.md','discovery.md'] for p in B.glob('lanes/*/'+n)):
  if p.parent==L:continue
  h=sha(p);t=p.read_text(errors='replace'); assert sha(p)==h
  for term in terms:
   i=t.lower().find(term.lower())
   if i>=0:out.append(dict(path=str(p),sha256=h,term=term,excerpt=t[max(0,i-180):i+500]))
 (L/'alias-history.json').write_text(json.dumps(out,indent=2))
 for x in out:print(x['path'].split('/')[-2],x['term'],x['excerpt'])
