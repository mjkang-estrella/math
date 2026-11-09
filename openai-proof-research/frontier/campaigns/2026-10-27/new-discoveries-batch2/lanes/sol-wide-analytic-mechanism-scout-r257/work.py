import pathlib,json,hashlib,shutil,datetime,urllib.request,time,re,subprocess,sys
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,o):
 p=L/n;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_text(o if isinstance(o,str) else json.dumps(o,indent=2,ensure_ascii=False))
def freeze(p,d):
 a=h(p);d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,d);b=h(p);c=h(d)
 assert a==b==c
 return dict(original=str(p),copy=str(d),sha256=a)
def get(url,name):
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical research source audit (bounded single request)'})
  with urllib.request.urlopen(req,timeout=28) as r:
   data=r.read(12000001);assert len(data)<=12000000
   p=L/'primary'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data)
   return dict(url=url,path=str(p),sha256=h(p),bytes=len(data),status=r.status,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 except Exception as e:return dict(url=url,error=str(e),time=datetime.datetime.now(datetime.timezone.utc).isoformat())
if sys.argv[1]=='init':
 a=[]
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md',R/'sources/upstream.json']:
  if p.exists():a.append(freeze(p,L/'administrative'/p.name))
 write('administrative/bindings.json',a)
 refs=[]
 for p in sorted((B/'lanes').glob('*/*')):
  if p.name.lower() in ['summary.md','scouting.md','discovery.md','review.md','progress.json'] and p.is_file() and p.stat().st_size<150000:
   refs.append({'path':str(p),'sha256':h(p)})
 write('history-bindings.json',refs)
 # Read reports only after their immutable hash binding.
 rows=[]
 for r in refs:
  p=pathlib.Path(r['path']);assert h(p)==r['sha256']
  s=p.read_text(errors='replace');rows.append({'path':str(p),'text':s})
 write('history-index.json',rows)
 print('bound reports',len(rows));print((L/'administrative/ledger.json').read_text()[-14000:]);print((L/'administrative/prior-campaign-context.json').read_text()[-16000:])
elif sys.argv[1]=='search':
 url='https://arxiv.org/search/?query='+urllib.parse.quote(sys.argv[2])+'&searchtype=all&abstracts=show&order=-announced_date_first&size=50'
 r=get(url,sys.argv[3]+'.html');write(sys.argv[3]+'.json',r)
 if 'path' in r:
  s=pathlib.Path(r['path']).read_text();print(re.sub('<[^>]+>',' ',s)[-58000:])
 else:print(r)
elif sys.argv[1]=='batchsearch':
 import html
 for i,q in enumerate(['"conjecture" "infinite divisibility"','"conjecture" "completely monotone"','"conjecture" "stochastic order"','"conjecture" "convexity" "2018"']):
  r=get('https://arxiv.org/search/?query='+urllib.parse.quote(q)+'&searchtype=all&abstracts=show&order=&size=50','batchsearch'+str(i)+'.html');write('batchsearch'+str(i)+'.json',r)
  if 'path' not in r: print(r);continue
  s=pathlib.Path(r['path']).read_text();out=[]
  for part in s.split('<li class="arxiv-result">')[1:]:
   out.append(html.unescape(re.sub('<[^>]+>',' ',part)).strip())
  write('search-results'+str(i)+'.json',out);print(q);print('\n'.join(x[:1800] for x in out))
elif sys.argv[1]=='compact':
 p=L/'history-index.json';p.unlink(missing_ok=True)
 print('removed temporary whole-report aggregation; immutable bindings retained')
elif sys.argv[1]=='list':
 for i in range(4):
  print('SEARCH',i)
  for s in json.loads((L/('search-results'+str(i)+'.json')).read_text()):
   s=re.sub(r'\s+',' ',s);print(s.split('Abstract :')[0])
elif sys.argv[1]=='screen':
 ids=sys.argv[2:];refs=json.loads((L/'history-bindings.json').read_text());hits=[]
 for r in refs:
  p=pathlib.Path(r['path']);assert h(p)==r['sha256'];s=p.read_text(errors='replace')
  for a in ids:
   if a.lower() in s.lower():
    j=s.lower().index(a.lower());hits.append(dict(query=a,path=str(p),excerpt=s[max(0,j-130):j+700]))
 write('history-screen-'+str(len(list(L.glob('history-screen-*.json'))))+'.json',hits)
 for a in ids:
  z=[r for r in hits if r['query']==a];print(a,len(z));print(json.dumps(z[:2],ensure_ascii=False))
elif sys.argv[1]=='fetch':
 rows=[]
 for a in sys.argv[2:]:
  r=get('https://arxiv.org/pdf/'+a,a+'.pdf');rows.append(r);print(r)
  if 'path' in r:
   p=pathlib.Path(r['path']);b=freeze(p,L/'frozen'/p.name);write('bindings/'+a+'.json',b)
   o=L/'texts'/(a+'.txt');o.parent.mkdir(exist_ok=True)
   z=subprocess.run(['pdftotext','-layout',str(L/'frozen'/p.name),str(o)],capture_output=True,timeout=30)
   assert h(p)==b['sha256']==h(L/'frozen'/p.name)
   if z.returncode:print(z.stderr.decode()[:1000])
 write('retrieval-'+sys.argv[2]+'.json',rows)
elif sys.argv[1]=='excerpts':
 for a in sys.argv[2:]:
  p=L/'texts'/(a+'.txt')
  if not p.exists():continue
  s=p.read_text();print('\nSOURCE',a,s[:1500])
  for m in list(re.finditer(r'(?i)conjecture|open problem|question [0-9]',s))[:18]:print(s[max(0,m.start()-150):m.start()+1900])
elif sys.argv[1]=='read':
 p=L/'texts'/(sys.argv[2]+'.txt');s=p.read_text().splitlines();a=int(sys.argv[3]);b=int(sys.argv[4]);print('\n'.join(f'{j+1}: {x}' for j,x in enumerate(s) if a<=j+1<=b))
elif sys.argv[1]=='questions':
 for a in sys.argv[2:]:
  p=L/'texts'/(a+'.txt');s=p.read_text();print('\nSOURCE',a,s[:650])
  lines=s.splitlines();hits=[j for j,x in enumerate(lines) if re.search(r'(?i)conjecture|problem [0-9]|question [0-9]',x)]
  print('LINES',hits)
  for j in hits[-6:]: print('\n'.join(lines[max(0,j-2):j+20]))
elif sys.argv[1]=='fresh':
 import html
 qs=sys.argv[2:] or ['"Rigidity of infinite exchangeable sequences with Gaussian marginals"','"Newman" "exchangeable" "Gaussian"','"fractional Gaussian noise" "positive"','"two-dimensional" "Gaussian squares" "divisibility"','"Wiener-Hopf" "determined"','"Ramanujan" "universally convex"','"critical Hawkes"','"Dyn-Farkhi"','"convolution polynomials" "Borel"','"least favorable noise"','"half-Cauchy" "HCM"']
 tag='target' if sys.argv[2:] else 'fresh'
 out=[]
 for i,q in enumerate(qs):
  r=get('https://arxiv.org/search/?query='+urllib.parse.quote(q)+'&searchtype=all&abstracts=show&order=-announced_date_first&size=50',tag+str(i)+'.html')
  row=dict(query=q,retrieval=r,results=[])
  if 'path' in r:
   for part in pathlib.Path(r['path']).read_text().split('<li class="arxiv-result">')[1:]:
    s=html.unescape(re.sub('<[^>]+>',' ',part));s=re.sub(r'\s+',' ',s);row['results'].append(s)
  out.append(row);print(q);print('\n'.join(x[:500] for x in row['results'][:10]))
 write(tag+'ness.json',out)
elif sys.argv[1]=='methods':
 out=[]
 for p in sorted((L/'texts').glob('*.txt')):
  s=p.read_text();matches=list(re.finditer(r'(?im)^\s*(?:Proof[ .:]|Proof of|Theorem [0-9]|Proposition [0-9])',s));chunks=[]
  for m in matches[:3]:chunks.append(s[m.start():m.start()+1500])
  out.append(dict(id=p.stem,titlepage=s[:1700],method_neighborhoods=chunks))
  if p.stem in ['1811.03827','1706.03975','1402.1059','1605.05479','2504.01562']:print(p.stem+'\n'+'\n'.join(chunks))
 write('method-excerpts.json',out)
elif sys.argv[1]=='chronology':
 out=[]
 for p in sorted((L/'texts').glob('*.txt')):
  r=get('https://arxiv.org/abs/'+p.stem,p.stem+'-abs.html');out.append(r)
 write('chronology-retrievals.json',out)
 print('retrieved',len(out),'failures',[r for r in out if 'error' in r])
