import os,json,hashlib,shutil,pathlib,sys,subprocess,urllib.request,datetime
L=pathlib.Path(__file__).parent
B=L.parent.parent
P=L.parent/'sol-polynomial-basins-breadth-depth-r237'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):
 p=L/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(x if isinstance(x,str) else json.dumps(x,indent=2))
def fetch(url,name):
 q=L/'sources'/name;q.parent.mkdir(exist_ok=True)
 try:
  r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceAudit/1.0'}),timeout=30)
  data=r.read(12000000)
  if b'captcha' in data[:10000].lower() or b'challenge-platform' in data[:10000].lower(): raise ValueError('challenge; stopped')
  q.write_bytes(data)
  cp=L/'frozen/live'/name;cp.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,cp);assert h(q)==h(cp)
  rec={'url':url,'path':str(q),'sha256':h(q),'status':r.status,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(q),str(q.with_suffix('.txt'))],check=True)
  return q
 except Exception as e:
  with (L/'failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
  return None
if sys.argv[1]=='get':
 q=fetch(sys.argv[2],sys.argv[3]);print(str(q));
 if q and not q.suffix=='.pdf':print(q.read_text()[:100000])
if sys.argv[1]=='read':
 p=L/sys.argv[2];print(p.read_text()[int(sys.argv[3]):int(sys.argv[4])])
if sys.argv[1]=='batch':
 for suffix in sys.argv[2:]:
  q=fetch('https://cs.uwaterloo.ca/journals/JIS/'+suffix,pathlib.Path(suffix).name)
  if q and q.suffix=='.pdf':
   t=q.with_suffix('.txt').read_text();import re
   print('\nSOURCE',suffix,'LENGTH',len(t))
   for m in list(re.finditer(r'(?i)conjecture|open problem|question [0-9]|problem [0-9]',t))[-16:]:print(t[max(0,m.start()-100):m.start()+1800])
if sys.argv[1]=='prior':
 q=fetch('https://export.arxiv.org/api/query?search_query=all:%22Curious%20Bounds%20for%20Floor%22&max_results=10','current-floors.xml')
 if q:print(q.read_text()[:30000])
if sys.argv[1]=='passages':
 import re
 for name in sys.argv[2:]:
  p=L/'sources'/name;t=p.read_text();print('\nSOURCE',name)
  for i,page in enumerate(t.split('\f'),1):
   if re.search(r'(Conjecture|Question|Problem) \d+\.',page): print('PAGE',i,page[:16000])
if sys.argv[1]=='pong':
 t=(L/'sources/pong11.txt').read_text();print(t[:14000]);print(t[-26000:])
if sys.argv[1]=='scan':
 import re
 links=re.findall(r'href="([^"]+\.pdf)"',(L/'sources/vol20.html').read_text())
 for suffix in links[int(sys.argv[2]):int(sys.argv[3])]:
  name=pathlib.Path(suffix).name
  q=L/'sources'/name
  if q.exists():continue
  q=fetch('https://cs.uwaterloo.ca/journals/JIS/'+suffix,name)
  if q:
   t=q.with_suffix('.txt').read_text();hits=list(re.finditer(r'(?:Conjecture|Question|Problem) \d+\.',t))
   if hits:print(suffix,[(m.group(),t[m.start():m.start()+600]) for m in hits[-4:]])
if sys.argv[1]=='history':
 import re
 aliases={'floors':r'floor.function.sums|wong7|Thanatipanonda|pong11|Jacobsthal.*Tverberg','diagonals':r'pinter3|Non.intersecting Diagonals','cfz':r'greene3|Non.Integer Numerators|cfz','trip':r'TRIP.Stern|garrity6','beatty':r'ballot22|Words on a Pair of Beatty','boolean':r'gav4|Bases in Dihedral','commuting':r'levit4|Hultman|Conjecture 72','alternating':r'toth25|Alternating Sums Concerning','whitney':r'mango4|Hankel.*Whitney','riordan':r'phulara3|B.sequence.*pseudo','coons':r'coons7|Extension of a Theorem of Duffin','width':r'davis6|Width.k Generalizations','ramsey':r'401 and Beyond|alm.pdf|Ramsey algebra search'}
 out=[]
 for lane in sorted(L.parent.iterdir()):
  if lane==L or not lane.is_dir():continue
  for name in ['SUMMARY.md','SCOUTING.md','discovery.md']:
   p=lane/name
   if not p.exists() or p.stat().st_size>250000:continue
   before=h(p);q=L/'frozen/history'/before
   if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
   assert h(q)==before==h(p)
   t=q.read_text(errors='replace');hits={a:[t[max(0,m.start()-150):m.start()+500] for m in list(re.finditer(rx,t,re.I))[:4]] for a,rx in aliases.items()}
   hits={a:v for a,v in hits.items() if v}
   if hits:out.append({'path':str(p),'frozen':str(q),'sha256':before,'hits':hits})
 write('history.json',out);print(json.dumps(out,indent=2)[:50000])
if sys.argv[1]=='currents':
 import urllib.parse,xml.etree.ElementTree as E
 qs=['au:Thanatipanonda AND all:floor','all:Jacobsthal AND all:Tverberg','all:%22non-intersecting diagonals%22','all:%22non-integer numerators%22','all:%22TRIP-Stern%22','au:Ballot AND all:Beatty','all:%22bases%22 AND au:Gavrylkiv','all:%22Hultman%22','au:Toth AND all:%22alternating sums%22','all:%22Whitney%22 AND all:%22Hankel%22','au:Phulara AND all:involution']
 for i,qu in enumerate(qs):
  qu=urllib.parse.unquote(qu);q=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(qu)+'&max_results=8','screen-'+str(i)+'.xml')
  if q:
   root=E.fromstring(q.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
   print(qu,[(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns)) for e in root.findall('a:entry',ns)])
if sys.argv[1]=='diagnostic':
 import itertools
 results=[];checks=0
 for m in range(1,25):
  lo=0;w=None
  for a in itertools.combinations_with_replacement(range(m),4):
   ss=[sum(a[i] for i in range(4) if mask>>i&1) for mask in range(16)]
   signs=[(-1)**(4-mask.bit_count()) for mask in range(16)]
   qs=[divmod(s,m) for s in ss];s=0
   for K in range(m):
    s+=sum(c*((K+t)//m) for c,t in zip(signs,ss))
    exact=sum(c*((K+1)*q+max(0,r+K+1-m)) for c,(q,r) in zip(signs,qs))
    assert s==exact;checks+=1
    if s<lo:lo=s;w=[a,K]
   assert s==0
  assert lo>=-3*(m//3)
  results.append({'m':m,'minimum':lo,'witness':w})
 write('exactchecks.json',{'status':'finite diagnostics only; not all-m certificate','m_range':[1,24],'tuples_K':checks,'results':results});print(results)
if sys.argv[1]=='lia':
 if (L/'lia-result.json').exists():shutil.copyfile(L/'lia-result.json',L/'lia-initial-failure.json')
 sys.path.insert(0,str(L/'tools'))
 try:
  import z3
  m,H=z3.Ints('m H');a=z3.Ints('a b c d');t=z3.Int('t');sol=z3.Solver();sol.set(timeout=180000)
  sol.add(m>=1,H>=1,H<=m,t>=0,m>=3*t,m<=3*t+2)
  sol.add(*[x>=0 for x in a],*[x<m for x in a],*[a[i]<=a[i+1] for i in range(3)])
  def clip(v):return z3.If(v<=0,0,z3.If(v>=H,H,v))
  S=z3.Sum([(-1)**(4-mask.bit_count())*z3.Sum([clip(z3.Sum([a[i] for i in range(4) if mask>>i&1])+H-q*m) for q in range(1,5)]) for mask in range(16)])
  sol.add(S < -3*t)
  write('all-m-query.smt2',sol.to_smt2());r=sol.check();write('lia-result.json',{'result':str(r),'reason_unknown':sol.reason_unknown(),'model':str(sol.model()) if r==z3.sat else None,'version':z3.get_version_string(),'scope':'untrusted solver diagnostic, not proof certificate'});print(r)
 except Exception as e:write('lia-result.json',{'error':str(e),'status':'failed route preserved'});print(e)
if sys.argv[1]=='compact':
 import re
 out={}
 for name in sys.argv[2:]:
  t=(L/'sources'/name).read_text();print('\nSOURCE',name)
  pats=r'Conjecture \d+\.|Theorem \d+\.|Problem \d+\.|Received |Published\s+in|conjecture|open question'
  matches=list(re.finditer(pats,t,re.I));out[name]=[]
  for ma in matches:
   if name in ['commuting-follow.txt','whitney-follow.txt'] and 'conjecture' not in ma.group().lower() and 'theorem' not in ma.group().lower():continue
   chunk=t[max(0,ma.start()-50):ma.start()+1600];out[name].append(chunk)
  print('\n'.join(out[name])[:18000])
 write('source-passages-'+sys.argv[2]+'.json',out)
if sys.argv[1]=='extras':
 import re,urllib.parse,xml.etree.ElementTree as E
 for i,qu in enumerate(['au:Coons AND all:Duffin','all:%22width-k%22 AND all:descents','au:Alm AND all:Ramsey','all:%22pseudo-involution%22 AND all:%22B-sequence%22']):
  q=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(qu)+'&max_results=12','extra-'+str(i)+'.xml')
  if q:
   root=E.fromstring(q.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'};print(qu,[(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns)) for e in root.findall('a:entry',ns)])
 for name in ['davis6.txt','greene3.txt','toth25.txt','ballot22.txt','phulara3.txt','garrity6.txt','levit4.txt']:
  t=(L/'sources'/name).read_text();print('\nSOURCE',name,t[:1800],t[-1100:])
  pats={'davis6.txt':['Gn,k','cyclic','Definition 8'], 'greene3.txt':['Theorem 24'], 'toth25.txt':['4.15'], 'levit4.txt':['Theorem 70']}
  for pat in pats.get(name,[]):
   idx=t.find(pat);print(t[max(0,idx-200):idx+6500])
if sys.argv[1]=='focused':
 import re
 for name,pat in [('greene3.txt','Theorem 24.'),('toth25.txt','4.15     Exponential'),('davis6.txt','cyclic width'),('phulara3.txt','Received'),('ballot22.txt','Received'),('garrity6.txt','Received'),('levit4.txt','Received')]:
  t=(L/'sources'/name).read_text();i=t.find(pat);print(name,pat,'offset',i,t[max(0,i-100):i+5000] if name in ['greene3.txt','toth25.txt'] else t[max(0,i-100):i+850])
if sys.argv[1]=='proof-object':
 sys.path.insert(0,str(L/'tools'));import z3
 z3.set_param(proof=True);sol=z3.Solver();sol.set(timeout=180000);sol.from_string((L/'all-m-query.smt2').read_text());r=sol.check();print(r)
 if r==z3.unsat:
  p=sol.proof().sexpr();write('z3-proof.sexpr',p);write('proof-object-status.json',{'result':str(r),'bytes':len(p),'independently_checked':False,'ordinary_proof':False,'version':z3.get_version_string()})
if sys.argv[1]=='freeze':
 bindings=[]
 for rel in ['SCOUTING.md','provenance.json','source-bindings.json']+['sources/'+s for s in ['wong7.pdf','wong7.txt']]:
  p=P/rel;q=L/'frozen/r237'/rel;q.parent.mkdir(parents=True,exist_ok=True);before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q);bindings.append({'original':str(p),'copy':str(q),'sha256':before})
 write('scientificbindings.json',bindings)
 for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
  shutil.copyfile(B/name,L/('administrative-'+name))
 write('administrative-read.json',{name:json.loads((B/name).read_text()) for name in ['ledger.json','prior-campaign-context.json']})
 print((L/'frozen/r237/SCOUTING.md').read_text()[:17000])
 print((L/'frozen/r237/sources/wong7.txt').read_text()[-34000:])
