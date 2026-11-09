import pathlib,hashlib,json,sys,datetime
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
L=B/'lanes/sol-polynomial-basins-breadth-depth-r237'
R=B/'lanes/sol-decimal-pairs-breadth-depth-r234'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='freeze':
 records=[]
 paths=[R/'SCOUTING.md',R/'provenance.json',R/'FAILURES.md']+list((R/'sources').glob('*.txt'))
 for p in paths:
  before=h(p); q=L/'frozen'/before/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());assert before==h(p)==h(q)
  records.append(dict(original=str(p),copy=str(q),sha256=before))
 (L/'source-bindings.json').write_text(json.dumps(records,indent=2))
 admin=[]
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
  if p.exists():
   q=L/'admin'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes());admin.append(dict(original=str(p),snapshot=str(q),sha256=h(q)))
 (L/'admin-snapshots.json').write_text(json.dumps(admin,indent=2))
 print((L/'frozen'/h(R/'SCOUTING.md')/'SCOUTING.md').read_text())
if sys.argv[1]=='more':
 rec=json.loads((L/'source-bindings.json').read_text())
 paths=[R/'sources/iterations.pdf',R/'sources/dismal.pdf',B/'lanes/sol-arithmetic-source-breadth-r231/SCOUTING.md']
 for p in paths:
  before=h(p);q=L/'frozen'/before/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());assert before==h(p)==h(q);rec.append(dict(original=str(p),copy=str(q),sha256=before))
 (L/'source-bindings.json').write_text(json.dumps(rec,indent=2))
 for name in ['iterations.txt','dismal.txt','SCOUTING.md']:
  matches=[r for r in rec if pathlib.Path(r['original']).name==name]
  for r in matches:
   if name=='dismal.txt':
    lines=pathlib.Path(r['copy']).read_text().splitlines();print('\n'.join(lines[175:250]+lines[295:312]+lines[650:687]+lines[1508:1516]))
   elif name=='iterations.txt' or 'r231' in r['original']:print(pathlib.Path(r['copy']).read_text())
if sys.argv[1]=='fetch':
 import urllib.request,subprocess
 name,url=sys.argv[2:4];d=L/'sources';d.mkdir(exist_ok=True);p=d/name
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research source verification contact local'})
  with urllib.request.urlopen(req,timeout=35) as res:
   data=res.read(12000000);p.write_bytes(data);receipt=dict(url=url,status=res.status,sha256=h(p),bytes=len(data),time=datetime.datetime.now(datetime.timezone.utc).isoformat())
  q=L/'frozen'/h(p)/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);assert h(q)==h(p)
  rec=json.loads((L/'source-bindings.json').read_text());rec.append(dict(original=str(p),copy=str(q),sha256=h(p)));(L/'source-bindings.json').write_text(json.dumps(rec,indent=2))
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(q),str(p.with_suffix('.txt'))],check=True)
  print(receipt)
 except Exception as e:receipt=dict(url=url,error=str(e));print(receipt)
 with (L/'retrieval-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
if sys.argv[1]=='batch':
 import re,subprocess
 index=(L/'sources/jis21.html').read_text();urls=list(dict.fromkeys(re.findall(r'href="(VOL21/[^\"]+\.pdf)"',index)))
 for url in urls[int(sys.argv[2]):int(sys.argv[3])]:
  subprocess.run([sys.executable,__file__,'fetch',url.split('/')[-1],'https://cs.uwaterloo.ca/journals/JIS/'+url],check=False)
if sys.argv[1]=='scan':
 import re
 for p in (L/'sources').glob('*.txt'):
  lines=p.read_text().splitlines();hits=[i for i,x in enumerate(lines) if re.search(r'Conjecture\s*\d|Question\s*\d|open problem|we conjecture',x,re.I)]
  if hits:
   print('\nFILE',p.name)
   for i in hits:print('\n'.join(lines[max(0,i-2):i+9]))
if sys.argv[1]=='history':
 import re
 terms=sys.argv[2:] or ['Borisov','nilpotency','polynomial maps','dismal']
 refs=[];hits=[]
 for p in (B/'lanes').glob('*/*'):
  if p.parent==L or p.name not in ['SUMMARY.md','SCOUTING.md','discovery.md']:continue
  digest=h(p);refs.append(dict(path=str(p),sha256=digest));s=p.read_text(errors='replace');assert h(p)==digest
  found=[t for t in terms if re.search(t,s,re.I)]
  if found:hits.append(dict(path=str(p),terms=found,excerpts=[x[:900] for x in s.splitlines() if any(re.search(t,x,re.I) for t in found)][:12]))
 out=dict(terms=terms,references=refs,hits=hits)
 (L/('history-'+str(len(terms))+'.json')).write_text(json.dumps(out,indent=2));print(json.dumps(hits,indent=2))
if sys.argv[1]=='queries':
 import urllib.parse,subprocess
 qs={'basins':'all:"polynomial maps" AND (all:"fixed points" OR all:"nilpotent")','lucas':'all:Lucasnomial AND au:Ballot','ipd':'all:"period-doubling" AND (all:inverse OR all:regular)','hyper':'au:Lasjaunias AND all:hyperquadratic','shiftfib':'all:"shifted Fibonacci"','floors':'au:Thanatipanonda AND all:floor','memory':'au:Young AND all:"game of memory"','harshad':'au:Nitica AND (all:Ramanujan OR all:Harshad)','cube':'au:Florez AND all:cube'}
 for name,q in qs.items():
  url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=12,sortBy='lastUpdatedDate',sortOrder='descending'))
  subprocess.run([sys.executable,__file__,'fetch','query-'+name+'.xml',url],check=False)
if sys.argv[1]=='metadata':
 import xml.etree.ElementTree as ET
 ns={'a':'http://www.w3.org/2005/Atom'}
 for p in (L/'sources').glob('query-*.xml'):
  print('\n',p.name)
  try:
   for e in ET.parse(p).getroot().findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:published',namespaces=ns),' '.join(e.findtext('a:title',default='',namespaces=ns).split()))
  except Exception as e:print(e)
 for name in ['wong7','ballot30','lasj5','stip8','nitica10','kreh6','young2','florez4']:
  p=L/'sources'/f'{name}.txt';lines=p.read_text().splitlines();print(name,'\n'.join(x for i,x in enumerate(lines) if 'Received' in x or 'Published in' in x or 'Journal of Integer Sequences,' in x and i>100))
if sys.argv[1]=='bind-final':
 records=json.loads((L/'source-bindings.json').read_text());known={r['original'] for r in records}
 for p in (L/'sources').iterdir():
  if str(p) in known:continue
  before=h(p);q=L/'frozen'/before/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.write_bytes(p.read_bytes())
  assert h(p)==h(q)==before;records.append(dict(original=str(p),copy=str(q),sha256=before,kind='derived-text' if p.suffix=='.txt' else 'retrieved-original'))
 (L/'source-bindings.json').write_text(json.dumps(records,indent=2))
 checks=[]
 for r in records:
  ok=h(pathlib.Path(r['original']))==h(pathlib.Path(r['copy']))==r['sha256'];assert ok;checks.append(dict(original=r['original'],copy=r['copy'],sha256=r['sha256'],unchanged=ok))
 for a,b in [('iterations.pdf','original-borisov.pdf'),('dismal.pdf','original-dismal.pdf')]:
  p=R/'sources'/a;q=L/'sources'/b;assert h(p)==h(q);checks.append(dict(cached=str(p),live=str(q),identical=True,sha256=h(p)))
 (L/'source-postread-checks.json').write_text(json.dumps(checks,indent=2));print('verified bindings',len(records))
if sys.argv[1]=='extract':
 import re
 docs={}
 for name in ['wong7','ballot30','lasj5','stip8','nitica10','kreh6','young2','florez4','memory-follow','hyper-follow','harshad-follow','original-borisov','borisov-follow','borisov-precursor']:
  p=L/'sources'/f'{name}.txt';s=p.read_text();pages=s.split('\f');hits=[]
  for i,page in enumerate(pages,1):
   if re.search('Conjecture|Question|Problem|Received|Published',page):hits.append(dict(pdf_page=i,text=page))
  docs[name]=dict(text_sha256=h(p),selected_pages=hits)
 (L/'source-passages.json').write_text(json.dumps(docs,indent=2));print('source passages retained')
