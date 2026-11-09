import pathlib, hashlib, json, sys, urllib.request, urllib.parse, datetime, subprocess, xml.etree.ElementTree as ET
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def log(rec):
 with (L/'provenance.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
def freeze(p,admin=False):
 h=sha(p); q=L/('administrative' if admin else 'sources')/(h[:12]+'-'+p.name);q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes());assert sha(q)==sha(p)==h
 log(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,administrative=admin));return q
def get(url,dest):
 try:
  with urllib.request.urlopen(url,timeout=30) as r:data=r.read(14000000)
  dest.write_bytes(data);log(dict(url=url,copy=str(dest.relative_to(L)),sha256=sha(dest),time=datetime.datetime.now(datetime.timezone.utc).isoformat()));return True
 except Exception as e:
  with (L/'failures.jsonl').open('a') as f:f.write(json.dumps(dict(url=url,error=str(e)))+'\n')
  print('FAIL',url,str(e));return False
if sys.argv[1]=='init':
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:freeze(B/n,True)
 for n in ['claude-wide-finite-algebraic-scout-r245','sol-wide-analytic-geometric-scout-r246','sol-wide-analytic-mechanisms-r247']:
  for f in ['SCOUTING.md','SUMMARY.md']:
   p=B/'lanes'/n/f
   if p.exists():q=freeze(p);print(q.read_text()[:35000])
if sys.argv[1]=='search':
 q=sys.argv[2];url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=35,sortBy='relevance'))
 dest=L/('search-'+hashlib.sha256(q.encode()).hexdigest()[:12]+'.xml')
 if get(url,dest):
  ns={'a':'http://www.w3.org/2005/Atom'}
  for e in ET.fromstring(dest.read_bytes()).findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns)[:650])
if sys.argv[1]=='get':
 (L/'sources').mkdir(exist_ok=True)
 for ident in sys.argv[2:]:
  p=L/'sources'/(ident+'.pdf')
  if get('https://arxiv.org/pdf/'+ident,p):
   h=sha(p);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);assert sha(p)==h
   lines=p.with_suffix('.txt').read_text().splitlines()
   for i,l in enumerate(lines):
    if any(t in l.lower() for t in ['conjecture','open question','open problem','question 1','question 2']):print(ident,i,'\n'+'\n'.join(lines[max(0,i-2):i+12]))
if sys.argv[1]=='history':
 terms=sys.argv[2:];refs=[];hits={t:[] for t in terms}
 for d in (B/'lanes').iterdir():
  if d==L:continue
  for n in ['SCOUTING.md','SUMMARY.md','discovery.md','review.md']:
   p=d/n
   if not p.exists():continue
   h=sha(p);refs.append(dict(path=str(p),sha256=h));s=p.read_text(errors='replace').lower();assert sha(p)==h
   for t in terms:
    if t.lower() in s:hits[t].append(str(p))
 (L/'history-references.json').write_text(json.dumps(refs,indent=2));(L/'history-hits.json').write_text(json.dumps(hits,indent=2));print(json.dumps(hits,indent=2))
if sys.argv[1]=='read':
 p=L/'sources'/(sys.argv[2]+'.pdf');h=sha(p);q=freeze(p);assert sha(p)==sha(q)==h
 t=p.with_suffix('.txt');th=sha(t);a=int(sys.argv[3]);b=int(sys.argv[4]);print('\n'.join(t.read_text().splitlines()[a:b]));assert sha(p)==sha(q)==h and sha(t)==th
if sys.argv[1]=='overview':
 for p in sorted((L/'sources').glob('*.txt')):
  h=sha(p);q=freeze(p);s=q.read_text().splitlines();print('\nFILE',p.name,'\n'+'\n'.join(s[:12]))
  for i,l in enumerate(s):
   if ('Conjecture' in l or 'Question' in l) and len(l)<180:print(i,'\n'+'\n'.join(s[i:i+9]))
  assert sha(p)==sha(q)==h
if sys.argv[1]=='probe':
 import importlib.util
 print({x:bool(importlib.util.find_spec(x)) for x in ['z3','scipy','sympy']})
if sys.argv[1]=='focus':
 for ident in sys.argv[2:]:
  p=L/'sources'/(ident+'.txt');q=freeze(p);h=sha(p);ls=q.read_text().splitlines();print('\nFILE',ident,'\n'+'\n'.join(ls[:18]))
  inds=[i for i,l in enumerate(ls) if any(t in l.lower() for t in ['conjecture.','conjecture 1','conjecture 2','conjecture 3','conjecture 4','conjecture 5','conjecture 6','we conjecture','theorem 1.','theorem 2.','theorem a','theorem b','open problem'])]
  for i in inds[:8]:print(i,'\n'+'\n'.join(ls[max(0,i-2):i+15]))
  assert sha(p)==sha(q)==h
if sys.argv[1]=='metadata':
 ids=sys.argv[2:];p=L/'chronology.xml'
 if get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'id_list':','.join(ids),'max_results':40}),p):
  ns={'a':'http://www.w3.org/2005/Atom'};out=[]
  for e in ET.fromstring(p.read_bytes()).findall('a:entry',ns):
   out.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
  (L/'chronology.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
