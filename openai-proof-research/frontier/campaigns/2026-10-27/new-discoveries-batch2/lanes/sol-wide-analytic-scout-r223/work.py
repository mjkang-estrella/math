from pathlib import Path
import json, hashlib, datetime, sys, shutil, urllib.request, subprocess
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):
 p.parent.mkdir(parents=True,exist_ok=True); p.write_text(x if isinstance(x,str) else json.dumps(x,indent=2))
def freeze(p,kind):
 q=L/kind/(p.parent.name+'--'+p.name); q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p)
 if not q.exists(): shutil.copyfile(p,q)
 assert sha(p)==sha(q)==h
 rows.append(dict(original=str(p),copy=str(q),sha256=h,kind=kind,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 return q
rows=[]
if sys.argv[1]=='init':
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md',R/'sources/upstream.json']:
  if p.exists():freeze(p,'administrative')
 for lane in ['sol-wide-analysis-scout-r221','sol-median-dynamics-breadth-depth-r1','sol-pade-breadth-depth-r1']:
  freeze(B/'lanes'/lane/'SCOUTING.md','frozen-reports')
 for p in [R/'sources/CONTENTS.md', R/'sources/preprints-tree.json']:
  if p.exists():freeze(p,'frozen-index')
 save(L/'freeze.json',rows)
 for row in rows:
  p=Path(row['copy'])
  if p.suffix=='.json' and 'ledger' in p.name:
   j=json.loads(p.read_text()); print('LEDGER',[(r.get('number'),r.get('title')) for r in j.get('accepted',[])])
  elif p.name.endswith('SCOUTING.md'):print(p.name,p.read_text()[:21000])
 print('ROOT',R)
elif sys.argv[1]=='catalogue':
 p=L/'frozen-index/sources--CONTENTS.md'
 lines=p.read_text().splitlines()
 import re
 hits=[x for x in lines if re.search(r'Bessel|Tur.n|log.concav|convex|inequal|probab|entropy|Mittag|hypergeom|geometr',x,re.I)]
 print('\n'.join(hits[:150]))
elif sys.argv[1]=='query':
 import urllib.parse,xml.etree.ElementTree as ET
 queries=sys.argv[2:] or ['all:"conjecture" AND all:"inequalities"','all:"conjecture" AND all:"special functions"','all:"conjecture" AND all:"probability"']
 for i,q in enumerate(queries):
  url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':0,'max_results':18,'sortBy':'submittedDate','sortOrder':'descending'})
  try:
   with urllib.request.urlopen(url,timeout=35) as f:data=f.read(3000000);status=f.status
   tag=hashlib.sha256(q.encode()).hexdigest()[:12];p=L/'retrieval'/('query-'+tag+'.xml');p.parent.mkdir(exist_ok=True);p.write_bytes(data)
   save(p.with_suffix('.json'),dict(url=url,status=status,sha256=sha(p),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
   root=ET.fromstring(data);ns={'a':'http://www.w3.org/2005/Atom'}
   for e in root.findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
  except Exception as e:save(L/'retrieval'/('query'+str(i)+'-failure.json'),dict(url=url,error=str(e)));print(str(e))
elif sys.argv[1]=='fetch':
 for ident in sys.argv[2:]:
  url='https://arxiv.org/pdf/'+ident;p=L/'primary'/(ident+'.pdf');p.parent.mkdir(exist_ok=True)
  try:
   if not p.exists():
    with urllib.request.urlopen(url,timeout=25) as f:data=f.read(16000000);status=f.status
    assert data.startswith(b'%PDF');p.write_bytes(data)
    save(p.with_suffix('.http.json'),dict(url=url,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=sha(p)))
   h=sha(p); t=p.with_suffix('.txt')
   subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=20)
   assert sha(p)==h
   save(p.with_suffix('.freeze.json'),dict(pdf=h,text=sha(t),frozen_before_read=True))
   s=t.read_text();print('\nSOURCE',ident,'HEAD',s[:600])
   import re
   for m in list(re.finditer(r'(?i)conjecture|open problem|question|remains open',s))[:12]:print('PAGE',s[:m.start()].count('\f')+1,s[max(0,m.start()-220):m.start()+900])
  except Exception as e:save(p.with_suffix('.failure.json'),dict(url=url,error=str(e)));print(ident,str(e))
elif sys.argv[1]=='read':
 import re
 for ident in sys.argv[2:]:
  p=L/'primary'/(ident+'.txt');s=p.read_text();j=json.loads(p.with_suffix('.freeze.json').read_text());assert sha(p)==j['text']
  print('\nSOURCE',ident)
  if ':' in ident:continue
  matches=list(re.finditer(r'(?im)^\s*(?:Conjecture|Question|Problem|Theorem)\s+\d',s))
  for m in matches[:9]:print('PDFPAGE',s[:m.start()].count('\f')+1,s[m.start():m.start()+1500])
  assert sha(p)==j['text']
elif sys.argv[1]=='history':
 base=B/'lanes/sol-fresh-source-discovery-r204'
 idx=freeze(base/'history-receipt.json','frozen-index')
 records=json.loads(idx.read_text())['records'];out=[];terms=['2609.39008','oscillatory','Csordas','Forgács','1505.00355','1401.7764','0910.0544','Bourne','Cagnetti','BCC lattice','Ramanujan R','general Bessel','cylinder function','Coulomb','parabolic cylinder','2609.25333']
 for r in records:
  p=base/r['copy'];assert sha(p)==r['sha256'];s=p.read_text(errors='replace')
  hits=[t for t in terms if t.lower() in s.lower()]
  if hits:out.append(dict(reference=str(p),sha256=r['sha256'],hits=hits,excerpts={t:s[max(0,s.lower().find(t.lower())-100):s.lower().find(t.lower())+350] for t in hits}))
  assert sha(p)==r['sha256']
 for p in sorted((B/'lanes/sol-wide-analysis-scout-r221/sources').glob('*SCOUTING.md')):
  q=freeze(p,'frozen-reports');s=q.read_text();hits=[t for t in terms if t.lower() in s.lower()]
  if hits:out.append(dict(reference=str(q),sha256=sha(q),hits=hits))
 save(L/'history-screen.json',dict(verified=len(records),terms=terms,hits=out,references=rows));print(json.dumps(out,indent=2)[:14000])
elif sys.argv[1]=='diagnostic':
 import numpy as np
 from scipy.special import jv,yv,jvp,yvp
 from scipy.optimize import brentq,minimize_scalar
 import math
 def minimum(mu,alpha):
  co,si=math.cos(alpha),math.sin(alpha)
  def c(x):return co*jv(mu,x)-si*yv(mu,x)
  xs=np.concatenate((np.geomspace(1e-12,1,240),np.linspace(1,mu+30,1400)))
  zeros=[];last=float(xs[0]);v=c(last)
  for xx in xs[1:]:
   w=c(xx)
   if v*w<0:zeros.append(brentq(c,last,float(xx),xtol=1e-13))
   if len(zeros)==2:break
   last=float(xx);v=w
  if len(zeros)<2:raise ValueError('roots not bracketed')
  def phi(x):
   y=x*(co*jvp(mu,x)-si*yvp(mu,x))/c(x)
   return 1+(y*y-mu*mu)/(x*x)
  opt=minimize_scalar(phi,bounds=(zeros[0]+1e-9,zeros[1]-1e-9),method='bounded',options={'xatol':1e-12})
  return dict(c=zeros[0],a=opt.x,b=opt.fun)
 out=[]
 for alpha in [math.pi*x for x in [.84,.9,.99,.9999,.99999999]]:
  for mu in [.1,.3,.5,1.,2.,5.,10.,20.]:
   z=minimum(mu,alpha);h=1e-4*mu;z['db']=(minimum(mu+h,alpha)['b']-minimum(mu-h,alpha)['b'])/(2*h)
   z.update(mu=mu,alpha=alpha);out.append(z)
 save(L/'diagnostic.json',dict(scope='floating diagnostics only, first two zeros bracketed on stated fixed meshes',rows=out,positive_derivatives=[x for x in out if x['db']>0]))
 print('completed',len(out),'positive',len([x for x in out if x['db']>0]),'exceptional',len([x for x in out if x['c']<x['mu']]))
elif sys.argv[1]=='metadata':
 import urllib.parse,xml.etree.ElementTree as ET
 ids=[p.stem for p in (L/'primary').glob('*.pdf')]
 url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'id_list':','.join(ids),'max_results':30})
 with urllib.request.urlopen(url,timeout=30) as f:data=f.read(3000000)
 p=L/'retrieval/versions.xml';p.write_bytes(data);save(p.with_suffix('.json'),dict(url=url,sha256=sha(p),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 ns={'a':'http://www.w3.org/2005/Atom'};out=[]
 for e in ET.fromstring(data).findall('a:entry',ns):
  out.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
 save(L/'chronology.json',out);print(json.dumps(out,indent=2)[:6000])
elif sys.argv[1]=='proof-excerpts':
 import re
 out=[]
 for p in sorted((L/'primary').glob('*.txt')):
  s=p.read_text();j=json.loads(p.with_suffix('.freeze.json').read_text());assert sha(p)==j['text']
  matches=list(re.finditer(r'(?im)^\s*Proof[ .o]',s))
  excerpts=[dict(page=s[:m.start()].count('\f')+1,text=s[m.start():m.start()+1400]) for m in matches[:2]]
  out.append(dict(source=p.stem,proofs=excerpts));assert sha(p)==j['text']
 save(L/'body-excerpts.json',out)
 print(json.dumps(out,indent=2)[:22000])
