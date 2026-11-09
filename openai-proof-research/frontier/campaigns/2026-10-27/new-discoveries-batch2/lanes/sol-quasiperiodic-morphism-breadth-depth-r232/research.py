import pathlib,hashlib,json,urllib.request,urllib.parse,time,sys,subprocess,re
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(url,name):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'ResearchSourceCheck/1.0'})
  with urllib.request.urlopen(req,timeout=35) as r:
   data=r.read(12000000);status=r.status;final=r.url
  p.write_bytes(data);p.chmod(0o444)
  row={'url':url,'final':final,'status':status,'bytes':len(data),'sha256':h(p),'file':str(p),'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 except Exception as e:row={'url':url,'failure':str(e),'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row));return p if 'sha256' in row else None
if sys.argv[1]=='queries':
 queries={
 'finite-geometry':'(ti:"blocking sets" OR ti:"Cameron-Liebler" OR ti:"saturating sets" OR ti:"KM-arcs") AND (all:conjecture OR all:problem)',
 'optimization':'(ti:"matroid" OR ti:"integer decomposition" OR ti:"discrete polymatroid") AND (all:conjecture OR all:problem)',
 'polynomial':'(ti:"Ehrhart" OR ti:"Kazhdan-Lusztig" OR ti:"independence polynomial") AND (all:conjecture OR all:problem)',
 'morphism':'all:quasiperiodic AND (all:morphism OR all:Richomme)'}
 for k,q in queries.items():
  p=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&start=0&max_results=12&sortBy=lastUpdatedDate&sortOrder=descending',k+'.xml')
  if p:
   import xml.etree.ElementTree as E
   root=E.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
   for e in root.findall('a:entry',ns): print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:published',namespaces=ns))
  time.sleep(3)
elif sys.argv[1]=='history':
 needles=['quasiperiod','Cameron','blocking set','saturating','KM-arc','Ehrhart','matroid','Kazhdan','independence polynomial','integer decomposition','polymatroid']
 out=[];bindings=[]
 for root in [B,B.parent.parent/'2026-10-25/thirty-proof-campaign']:
  if not root.exists():continue
  for p in root.glob('lanes/*/*'):
   if p.name not in ['SUMMARY.md','discovery.md','SCOUTING.md']:continue
   if p.parent==L:continue
   before=h(p);t=p.read_text(errors='replace');after=h(p)
   assert before==after
   hits=[(i+1,line[:700]) for i,line in enumerate(t.splitlines()) if any(n.lower() in line.lower() for n in needles)]
   bindings.append({'path':str(p),'sha256':before,'bytes':p.stat().st_size})
   if hits:out.append({'path':str(p),'hits':hits[:15]})
 (L/'history-bindings.json').write_text(json.dumps(bindings,indent=2));(L/'history-screen.json').write_text(json.dumps(out,indent=2));print('files',len(bindings));print(json.dumps(out,indent=2)[:22000])
elif sys.argv[1]=='pdfs':
 for pair in sys.argv[2:]:
  name,identifier=pair.split('=',1);p=fetch('https://arxiv.org/pdf/'+identifier,name+'.pdf')
  if p:
   before=h(p);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);assert h(p)==before
  time.sleep(3)
elif sys.argv[1]=='url': fetch(sys.argv[2],sys.argv[3])
