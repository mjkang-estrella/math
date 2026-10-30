import sys,json,re,hashlib,datetime,urllib.request,gzip,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='init':
 bases=[L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json' for k in [170,172]]
 known={};br=[]
 for p in bases:
  b=p.read_bytes();br.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
 paths=set(known)
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','DECISION.md']:
    if (d/n).is_file():paths.add(str((d/n).relative_to(R)))
 rows=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();r=[p,sha(b),len(b)];rows.append(r)
  if known.get(p)!=r[1:]:changed.append(r)
 save('history-receipt.json',dict(utc=now(),bases=br,records=rows,changed=changed,missing=missing,limits='Qualified inherited ORIGINAL sets; no new echo exclusions; all r111-r113 originals retained. Bounded coverage.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  j=json.loads(b) if n.endswith('.json') else None
  print(n, len(b),list(j) if isinstance(j,dict) else b[:400].decode())
 for k,n in [(170,'history-qualification.json'),(172,'inherited-history-qualification.json')]:
  (L/f'qualification-r{k}.json').write_bytes((L.parent/f'sol-fresh-source-discovery-r{k}'/n).read_bytes())
 print('history',len(rows),'changed',len(changed),'missing',len(missing))
elif sys.argv[1]=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-150):m.end()+300] for m in ms[:8]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits,indent=2)[:22000])
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   assert not any(v in u.lower() for v in ['github','codeload','sciencedirect','google.'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='extract':
 for p in (L/'sources').glob('*.pdf'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[]
  def handle_data(self,s):self.out.append(s)
 for f in (L/'sources').glob('*.html'):
  p=P();p.feed(f.read_text());f.with_suffix('.html.txt').write_text('\n'.join(p.out))
elif sys.argv[1]=='registry':
 pat=re.compile(r'Two.inequalities.for.the.medians|Improvements.of.two.inequalities|Jian.Liu|Erd.s.Mordell|median.*triangle|triangle.*median|jmi.2020.14.11|s13660.015.0947',re.I);out=[]
 p=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
 for r in json.loads(p.read_text())['records']:
  f=Path(r['path']);b=f.read_bytes();s=gzip.decompress(b).decode() if f.suffix=='.gz' else b.decode()
  try:
   j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else []
   hits=[x for x in items if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[x for x in s.splitlines() if pat.search(x.split('\t')[-1])]
  out.append(dict(path=str(f),sha256=sha(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),records=out,pattern=pat.pattern,limits='Cached catalogue/path screen only, never body or current clearance. Historical coverage PARKED. No unavailable GitHub retry.'))
 print([(r['path'],len(r['hits'])) for r in out])
