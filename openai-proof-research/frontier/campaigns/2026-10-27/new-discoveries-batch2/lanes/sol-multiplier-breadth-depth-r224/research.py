import pathlib,json,hashlib,urllib.request,urllib.parse,datetime,subprocess,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(j,p):p.write_text(json.dumps(j,indent=2))
def fetch(url,name):
 d=L/'retrieval';d.mkdir(exist_ok=True);p=d/name
 if p.exists():raise RuntimeError('no repeat '+name)
 row={'url':url,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-research/1.0'}),timeout=35) as r:data=r.read(12000000);row['status']=r.status
  p.write_bytes(data);row.update(sha256=sha(p),bytes=len(data))
 except Exception as e:row['error']=str(e)
 save(row,d/(name+'.receipt.json'));print(row)
def bind(p,q):
 h=sha(p);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());assert sha(p)==sha(q)==h
 return dict(original=str(p),copy=str(q),sha256=h)
if sys.argv[1]=='bind':
 rows=json.loads((L/'freeze.json').read_text())
 p=B/'lanes/sol-wide-analytic-scout-r223/primary'
 for f in p.glob('*1505.00355*'):
  rows.append(bind(f,L/'primary'/f.name))
 save(rows,L/'freeze.json');print(rows[-4:])
elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
elif sys.argv[1]=='extract':
 p=L/'retrieval'/sys.argv[2];h=sha(p);q=p.with_suffix('.txt')
 subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);assert sha(p)==h
 save({'pdf':str(p),'pdf_sha256':h,'text':str(q),'text_sha256':sha(q)},q.with_suffix('.freeze.json'))
elif sys.argv[1]=='history':
 terms=['multiplier','csord','forg','laguerre','square.root','sqrt','1505.00355','hyperbolic complete','infinite divisib','entropy power','covariogram','torsion','Steiner','Minkowski','Rademacher','small.ball','persistence','heat content']
 import re
 rows=[];hits=[]
 for root in [B, B.parent.parent.parent.parent/'sources']:
  for p in root.rglob('*'):
   if L in p.parents or not p.is_file() or p.suffix not in ['.md','.json','.txt'] or p.stat().st_size>4000000:continue
   # Avoid generated replay/recursive copies; alias screen includes every unique body.
   h=sha(p)
   if h in {r['sha256'] for r in rows}:continue
   s=p.read_text(errors='replace');matched=[t for t in terms if re.search(t,s,re.I)]
   assert sha(p)==h;rows.append({'path':str(p),'sha256':h})
   if matched:
    lines=[line[:500] for line in s.splitlines() if any(re.search(t,line,re.I) for t in matched)]
    hits.append({'path':str(p),'terms':matched,'lines':lines[:12]})
 save(rows,L/'history-bindings.json');save(hits,L/'history-hits.json');print(len(rows),len(hits))
