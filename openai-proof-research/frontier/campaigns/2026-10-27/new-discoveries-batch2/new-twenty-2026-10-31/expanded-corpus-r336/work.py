import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120,120))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3,6*1024**3))
import pathlib, json, hashlib, time, sys, atexit, datetime, urllib.request, urllib.error
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
mode=sys.argv[1]
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,d): (P/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def finish():
 u=resource.getrusage(resource.RUSAGE_SELF)
 c=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (P/'resources.jsonl').open('a') as f: f.write(json.dumps(dict(argv=sys.argv,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),affinity=sorted(os.sched_getaffinity(0)),cpu_limit=120,AS_limit=6*1024**3,external_wall_limit=140,wall=time.monotonic()-start,self_cpu=u.ru_utime+u.ru_stime,self_peak_RSS_KiB=u.ru_maxrss,reaped_children_cpu=c.ru_utime+c.ru_stime,reaped_child_highwater_KiB=c.ru_maxrss,telemetry='self and reaped child high-water only; not concurrent group/cgroup/service peak'))+'\n')
if mode=='links':
 import re
 t=(P/sys.argv[2]).read_text()
 for m in re.finditer(r'href=[\"\x27]([^\"\x27]+)[\"\x27]',t):
  if any(s.lower() in t[max(0,m.start()-150):m.end()+250].lower() for s in sys.argv[3:]): print(t[max(0,m.start()-150):m.end()+250])
if mode=='registry-screen':
 import re
 names=['5b25a2f3f38031df.html','c199dab1fb045499.html','a209d5dc0c353563.html','460e6da8f448477a.html','a0f49158337a49a5.html']
 pats=['bicircular','Dickson','Hermitian','Zagreb','Reeb','Arnoux','Forking','LE-cactus']
 out=[]
 for n in names:
  t=(P/n).read_text(); heads=sorted(set(re.findall(r'"currentOid":"([a-f0-9]{40})"',t)))
  hits={s:[t[max(0,m.start()-150):m.start()+350] for m in list(re.finditer(re.escape(s),t,re.I))[:10]] for s in pats}
  out.append(dict(file=n,heads=heads,hits=hits,scope='current public page or routing catalogue only, no recursive tree/proof clearance'))
 print(json.dumps(out,ensure_ascii=False,indent=2));save('registry-screen.json',out)
 root=P.parents[5];t=(root/'sources/CONTENTS.md').read_text(); out=[]
 for s in pats:
  for m in list(re.finditer(re.escape(s),t,re.I))[:10]: out.append(dict(term=s,text=t[max(0,m.start()-200):m.start()+500]))
 save('pinned-catalogue-screen.json',out); print('PINNED',json.dumps(out,ensure_ascii=False))
if mode=='excerpt-part':
 d=json.loads((P/'target-excerpts.json').read_text())
 for row in d[int(sys.argv[2]):int(sys.argv[3])]:
  print(row['url'])
  for e in row['excerpts'][:3]: print(e['text'])
atexit.register(finish)
mode=sys.argv[1]
if mode=='slice':
 t=(P/sys.argv[2]).read_text(); a=int(sys.argv[3]); b=int(sys.argv[4]); print(t[a:b])
if mode=='target-excerpts':
 import re
 receipts=[json.loads(s) for s in (P/'http.jsonl').read_text().splitlines()]
 inventory=[]
 for r in receipts:
  if '/html/' not in r['url'] or not r.get('file'): continue
  name=r['file']; tfile=P/(name+'.txt')
  if not tfile.exists():
   print('NEEDS_CONVERSION',name); continue
  t=tfile.read_text(); ms=list(re.finditer(r'Conjecture\s+(?:\d|[A-Z])|conjecture that|conjecture is|Open Problem',t))
  excerpts=[dict(offset=m.start(),text=t[max(0,m.start()-180):m.start()+1400]) for m in ms[:8]]
  inventory.append(dict(url=r['url'],file=name,text_characters=len(t),excerpts=excerpts,depth='selected conjecture and surrounding statement context only; not all proof bodies'))
  print('SOURCE',r['url'])
  for x in excerpts[:3]: print(x['offset'],x['text'])
 save('target-excerpts.json',inventory)
if mode=='convert-all':
 import subprocess
 for r in map(json.loads,(P/'http.jsonl').read_text().splitlines()):
  if r.get('file','').endswith('.html') and '/html/' in r['url']:
   z=subprocess.run([sys.executable,'-I','-B',str(P/'work.py'),'snips',r['file'],'__NO_MATCH__'],capture_output=True,timeout=10)
   print(r['file'],z.returncode)
if mode=='registries':
 root=P.parents[5]
 print('ROOT',root)
 for name in ('sources/upstream.json','sources/CONTENTS.md'):
  f=root/name
  if f.exists():
   t=f.read_text(); print(name,t[:4500]); save(name.replace('/','-')+'.receipt.json',dict(path=str(f),bytes=f.stat().st_size,sha256=sha(f.read_bytes()),depth='pinned revision or catalogue routing'))
if mode=='pdf':
 import subprocess
 for n in sys.argv[2:]:
  r=subprocess.run(['pdftotext','-layout',str(P/n),'-'],capture_output=True,timeout=40)
  print(n,'exit',r.returncode,'bytes',len(r.stdout)); (P/(n+'.txt')).write_bytes(r.stdout)
  print(r.stdout.decode()[:42000])
if mode in ('read','snips'):
 from html.parser import HTMLParser
 class Parser(HTMLParser):
  def __init__(self): super().__init__(); self.out=[]; self.skip=0
  def handle_starttag(self,t,a):
   if t in ('script','style'): self.skip+=1
   if t in ('p','div','section','h1','h2','h3','tr'): self.out.append('\n')
   if t in ('math','img'):
    d=dict(a)
    if d.get('alttext') or d.get('alt'): self.out.append(' '+d.get('alttext',d.get('alt',''))+' ')
  def handle_endtag(self,t):
   if t in ('script','style'): self.skip-=1
  def handle_data(self,d):
   if not self.skip: self.out.append(d)
 for name in (sys.argv[2:3] if mode=='snips' else sys.argv[2:]):
  f=P/name
  if f.suffix=='.html':
   parser=Parser(); parser.feed(f.read_text()); t=''.join(parser.out); (P/(name+'.txt')).write_text(t)
  else: t=f.read_text()
  print('FILE',name,'CHARS',len(t))
  if mode=='read': print(t)
  else:
   import re
   for term in sys.argv[3:]:
    matches=list(re.finditer(re.escape(term),t,re.I)); print('TERM',term,'matches',len(matches))
    for m in matches[:14]: print('OFFSET',m.start(),t[max(0,m.start()-700):m.start()+3300])
if mode=='history-summary':
 for h in json.loads((P/'history-hits.json').read_text()):
  d=json.loads(h['text'])
  if isinstance(d,dict):
   for k,v in d.items():
    s=json.dumps(v,ensure_ascii=False)
    if any(n.lower() in s.lower() for n in h['needles']): print(h['path'],k,s[:5000])
if mode=='extract':
 r=(P/'reservation.json').read_bytes(); expected=(P/'reservation.sha256').read_text().strip(); assert sha(r)==expected
 ids=json.loads(r)['ids']; assert len(ids)==len(set(ids))==20
 save('reservation-before.json',dict(sha256=sha(r),expected=expected,ids=ids,verified=True))
 base=P.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 found={}
 for f in sorted(base.glob('mathdb-normalized-chunk-*.jsonl')):
  b=f.read_bytes(); h=sha(b)
  for line,raw in enumerate(b.splitlines(keepends=True),1):
   d=json.loads(raw); i=d.get('id',d.get('mathdb_id'))
   if i is not None and int(i) in ids:
    i=int(i); assert i not in found; assert raw.endswith(b'\n'); (P/f'{i}.raw.jsonl').write_bytes(raw)
    found[i]=dict(chunk=str(f),one_based_line=line,chunk_sha256=h,raw_sha256=sha(raw),final_newline=True,parsed_canonical_sha256=sha(json.dumps(d,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),record=d)
 assert set(found)==set(ids),list(found)
 save('literal-provenance.json',found)
 for i in ids: print(i,json.dumps(found[i]['record'],ensure_ascii=False))
elif mode=='history':
 ids=json.loads((P/'reservation.json').read_text())['ids']; rows=json.loads((P/'reservation.json').read_text())['rows']; needles=[str(i) for i in ids]+[r['source_url'].split('/')[-1] for r in rows]+['bicircular','LE-cactus','Frobenius type','Zagreb','Reeb graph','Arnoux']
 receipts=[]; hits=[]
 for s in json.loads((P/'historical-results-allowlist.json').read_text()):
  if 'crown-vnumber' in s or 'transitive-bunkbed-formal-pi-r1' in s: continue
  f=pathlib.Path(s)
  if not f.is_file(): continue
  b=f.read_bytes(); t=b.decode(); receipts.append(dict(path=s,bytes=len(b),sha256=sha(b),depth='bounded ID/source-family text screening of completed allowlist result metadata'))
  matching=[n for n in needles if n.lower() in t.lower()]
  if matching: hits.append(dict(path=s,needles=matching,text=t))
 save('history-read-inventory.json',receipts); save('history-hits.json',hits)
 for h in hits: print(h['path'],h['needles'],h['text'][:14000])
 for f in [P.parents[1]/'ledger.json',P.parent/'ledger.json',P.parent/'STATUS.md']:
  if f.is_file():
   t=f.read_text(); print('SCALAR',str(f),t[:200] if f.suffix=='.md' else {k:v for k,v in json.loads(t).items() if isinstance(v,(int,float,str,bool))})
elif mode=='fetch':
 for url in sys.argv[2:]:
  receipt=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='GET')
  try:
   req=urllib.request.Request(url,headers={'User-Agent':'Public mathematical research (read only)'})
   with urllib.request.urlopen(req,timeout=35) as r:
    b=r.read(20*1024**2+1); receipt.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'),bytes=len(b),sha256=sha(b),complete=len(b)<=20*1024**2)
   name=sha(url.encode())[:16]+('.pdf' if b.startswith(b'%PDF') else '.html'); (P/name).write_bytes(b); receipt['file']=name
  except Exception as e: receipt.update(error=str(e),status=getattr(e,'code',None))
  with (P/'http.jsonl').open('a') as f: f.write(json.dumps(receipt)+'\n')
  print(json.dumps(receipt),flush=True)
