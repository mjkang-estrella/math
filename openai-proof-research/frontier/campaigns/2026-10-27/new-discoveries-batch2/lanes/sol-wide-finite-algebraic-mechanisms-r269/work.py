import os,sys,json,hashlib,pathlib,datetime,urllib.request,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='freeze':
 refs=[]
 for name in ['sol-wide-new-source-mechanisms-r266','sol-wide-finite-structural-mechanisms-r262','sol-wide-finite-arithmetic-mechanisms-r260','sol-wide-cross-family-mechanisms-r263']:
  p=L.parent/name/'SCOUTING.md'; h=sha(p); q=L/'frozen'/name/'SCOUTING.md';q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());assert sha(p)==h==sha(q);refs.append(dict(original=str(p),copy=str(q),sha256=h))
 (L/'admin').mkdir(exist_ok=True)
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[2]/'AGENTS.md']:
  if p.exists(): (L/'admin'/p.name).write_bytes(p.read_bytes())
 dump(L/'bindings.json',refs)
 print(json.dumps(refs,indent=2))
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:4];p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-audit/1.0'}),timeout=25) as r:
   data=r.read(9000000);status=r.status;final=r.url
  if b'challenge' in data[:3000].lower() or b'captcha' in data[:3000].lower(): raise RuntimeError('challenge; STOP route')
  p.write_bytes(data);rec=dict(url=url,final=final,status=status,path=str(p),sha256=sha(p),bytes=len(data),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 except Exception as e:rec=dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
elif sys.argv[1]=='text':
 p=L/'primary'/sys.argv[2];h=sha(p);q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);assert sha(p)==h
 with (L/'derived.jsonl').open('a') as f:f.write(json.dumps(dict(source=str(p),sha256=h,text=str(q),text_sha256=sha(q)))+'\n')
elif sys.argv[1]=='verify-inputs':
 for r in json.loads((L/'bindings.json').read_text()):assert sha(pathlib.Path(r['original']))==r['sha256']==sha(pathlib.Path(r['copy']))
 print('all frozen historical originals/copies match')
elif sys.argv[1]=='list':
 import xml.etree.ElementTree as E
 root=E.parse(L/'primary'/sys.argv[2]);ns={'a':'http://www.w3.org/2005/Atom'}
 for e in root.findall('a:entry',ns):
  print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),' '.join(e.findtext('a:summary',namespaces=ns).split())[:1100])
elif sys.argv[1]=='batch':
 for ident in sys.argv[2:]:
  subprocess.run([sys.executable,str(__file__),'fetch','https://arxiv.org/pdf/'+ident,ident+'.pdf'],check=True)
  if (L/'primary'/(ident+'.pdf')).exists():subprocess.run([sys.executable,str(__file__),'text',ident+'.pdf'],check=True)
elif sys.argv[1]=='history':
 needles=['1201.0529','1201.0774','1201.1137','1201.2712','1201.3060','1201.4153','0501046','0501356','0501446','0501451','0501465','0502326','2301.00434','2301.01137','2301.01331','2301.01473','global sum','commuting matrices','cosets','cop pebbling','berge-tur','gal conjecture']
 refs=[];hits=[]
 for p in B.parent.parent.rglob('*.md'):
  if L in p.parents or p.name not in ['SCOUTING.md','SUMMARY.md','STATUS.md','discovery.md']:continue
  if 'frozen' in p.parts or 'extracted' in p.parts or 'verification' in p.parts:continue
  if p.stat().st_size>200000:continue
  h=sha(p);data=p.read_text(errors='replace');assert sha(p)==h;refs.append(dict(path=str(p),sha256=h))
  for i,line in enumerate(data.splitlines(),1):
   if any(n in line.lower() for n in needles):hits.append(dict(path=str(p),line=i,text=line[:1300]))
 dump(L/'history-bindings.json',refs);dump(L/'history-hits.json',hits);print(len(refs),'reports',len(hits),'hits');print(json.dumps(hits[:30],indent=2))
elif sys.argv[1]=='prior':
 import urllib.parse
 queries={'global-sum':'ti:"global sum" OR (au:Faber AND all:communication)','berge':'au:Gerbner AND (all:"non-degenerate" OR all:"nondegenerate")','cop':'all:"cop pebbling"','golod':'ti:Golod AND au:Katthan','stretch':'ti:"Littlewood-Richardson polynomials"'}
 for name,query in queries.items():
  url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=query,start=0,max_results=12,sortBy='submittedDate',sortOrder='descending'))
  subprocess.run([sys.executable,str(__file__),'fetch',url,'prior-'+name+'.xml'],check=True)
  subprocess.run([sys.executable,str(__file__),'list','prior-'+name+'.xml'],check=True)
elif sys.argv[1]=='receipts':
 import xml.etree.ElementTree as E
 ns={'a':'http://www.w3.org/2005/Atom'};entries=[]
 for p in (L/'primary').glob('*.xml'):
  for e in E.parse(p).findall('a:entry',ns):
   entries.append(dict(id=e.findtext('a:id',namespaces=ns),title=e.findtext('a:title',namespaces=ns),published=e.findtext('a:published',namespaces=ns),updated=e.findtext('a:updated',namespaces=ns),authors=[a.findtext('a:name',namespaces=ns) for a in e.findall('a:author',ns)]))
 dump(L/'chronology.json',entries)
 receipts=[]
 for r in map(json.loads,(L/'derived.jsonl').read_text().splitlines()):
  p=pathlib.Path(r['source']);q=pathlib.Path(r['text']);assert sha(p)==r['sha256'] and sha(q)==r['text_sha256']
  pages=q.read_text().split('\f');hits=[]
  for i,page in enumerate(pages,1):
   lines=[s.strip()[:180] for s in page.splitlines() if any(t in s for t in ['Conjecture','Theorem','Problem A','Problem B','Problem C','Question 1.'])]
   if lines:hits.append(dict(pdf_page=i,labels=lines[:10]))
  receipts.append(dict(**r,pages=hits))
 dump(L/'source-receipts.json',receipts)
 for name in ['ledger.json','prior-campaign-context.json']:
  d=json.loads((L/'admin'/name).read_text());print(name,[(v.get('number'),v.get('title',v.get('source_target'))) for v in d['accepted']])
 print('PDF/text original bindings verified:',len(receipts))
