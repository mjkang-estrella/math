import pathlib,sys,json,hashlib,urllib.request,urllib.parse,datetime,subprocess,concurrent.futures
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(pair):
 name,url=pair;p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=25) as r:
   data=r.read(12000000);row.update(status=r.status,final_url=r.url)
  p.write_bytes(data);row.update(sha256=h(p),bytes=len(data))
  q=L/'frozen'/name;q.write_bytes(data);assert h(q)==h(p);row['copy']=str(q.relative_to(L))
 except Exception as e:row['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 return row
if sys.argv[1]=='query':
 q=sys.argv[2];r=fetch((sys.argv[3]+'.xml','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=12&sortBy=relevance'))
 print(r)
 if 'copy'in r:
  import xml.etree.ElementTree as E
  root=E.parse(L/r['copy']);ns={'a':'http://www.w3.org/2005/Atom'}
  for x in root.findall('a:entry',ns):print(x.findtext('a:id',namespaces=ns),x.findtext('a:title',namespaces=ns),x.findtext('a:published',namespaces=ns))
elif sys.argv[1]=='get':
 print(fetch((sys.argv[2],sys.argv[3])))
elif sys.argv[1]=='batch':
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
  for r in ex.map(fetch,[(n+'.pdf','https://arxiv.org/pdf/'+n) for n in sys.argv[2:]]):print(r)
elif sys.argv[1]=='history':
 terms=sys.argv[2:];rows=[];hits=[]
 for d in L.parent.iterdir():
  if not d.is_dir() or d==L:continue
  for p in d.iterdir():
   if p.name.lower() not in ['scouting.md','summary.md','discovery.md'] or not p.is_file() or p.stat().st_size>120000:continue
   before=h(p);data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==before
   # Immutable-reference freeze before scientific term inspection; no archive duplication.
   rows.append({'path':str(p),'sha256':before})
   t=data.decode(errors='replace');found=[s for s in terms if s.lower() in t.lower()]
   if found:hits.append({'path':str(p),'terms':found,'excerpts':[t[max(0,t.lower().find(s.lower())-120):t.lower().find(s.lower())+300] for s in found]})
   assert h(p)==before
 (L/'history-screen.json').write_text(json.dumps({'references':rows,'terms':terms,'hits':hits},indent=2));print(json.dumps(hits,indent=2));print('screened',len(rows))
elif sys.argv[1]=='extract':
 for n in sys.argv[2:]:
  p=L/'frozen'/n;before=h(p);q=L/'frozen'/(n+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);assert h(p)==before
  with (L/'extractions.jsonl').open('a') as f:f.write(json.dumps({'pdf':n,'sha256':before,'text':q.name,'text_sha256':h(q)})+'\n')
elif sys.argv[1]=='read':
 for n in sys.argv[2:]:
  p=L/'frozen'/n;t=p.read_text();lines=t.splitlines();print('\nSOURCE',n)
  for i,line in enumerate(lines):
   if any(w in line.lower() for w in ['conjectur','open problem','question','problem 1','problem 2']): print('\n',i+1,'\n','\n'.join(lines[max(0,i-3):i+12]))
