from pathlib import Path
import sys,json,hashlib,datetime,re,urllib.request,subprocess
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='init':
 known={};bases=[]
 for k in [181,180,179,178,170]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json';b=p.read_bytes();bases.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
 paths=set(known)
 for p in R.rglob('*.md'):
  if L not in p.parents and p.name.lower() in ['summary.md','discovery.md','proof.md','review.md','decision.md']:paths.add(str(p.relative_to(R)))
 rows=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();r=[p,sha(b),len(b)];rows.append(r)
  if known.get(p)!=r[1:]:changed.append(r)
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,qualification='All inherited qualified originals retained, including r111–113. Conservative copy overinclusion; no echo/date/lane exclusions.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 inv=[]
 for p in B.rglob('*'):
  if L in p.parents or not p.is_file() or p.name not in ['http.jsonl','failures.json','access.jsonl']:continue
  b=p.read_bytes();bad=[s[:1000] for s in b.decode(errors='replace').splitlines() if re.search('403|429|418|challenge|CERTIFICATE_VERIFY_FAILED',s,re.I)]
  if bad:inv.append(dict(path=str(p),sha256=sha(b),failures=bad))
 save('inherited-access.json',inv)
 print('history',len(rows),'changed',len(changed),'missing',len(missing),'denied inventories',len(inv))
elif sys.argv[1]=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+250] for m in ms[:3]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print('hits',len(hits));print(json.dumps(hits[:15],indent=2)[:14000])
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 denied=(L/'inherited-access.json').read_text()
 for a in sys.argv[2:]:
  n,u=a.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   assert not any(v in u.lower() for v in ['github','codeload','sciencedirect','google.','ieeexplore','openreview','d-nb.info','arxiv.org/search'])
   assert u not in denied,'Inherited denied URL'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=22) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='extract':
 for p in (L/'sources').glob('*.pdf'):
  if not p.read_bytes().startswith(b'%PDF'):print('SKIP non-PDF response',p.name);continue
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
elif sys.argv[1]=='registry':
 import gzip
 pat=re.compile('Legendre|Pouso|Segura|Kohler|Lucardesi|Quadrature|Petras',re.I);out=[]
 p=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
 for r in json.loads(p.read_text())['records']:
  f=Path(r['path']);b=f.read_bytes();s=gzip.decompress(b).decode() if f.suffix=='.gz' else b.decode()
  try:
   j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else [];hits=[x for x in items if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[x for x in s.splitlines() if pat.search(x.split('\t')[-1])]
  out.append(dict(path=str(f),sha256=sha(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),pattern=pat.pattern,records=out,limits='Cached names only. Current heads inaccessible by authorization; capped historical intervals and missing merge trees PARKED. No novelty clearance inferred.'))
 print('cached registries',len(out),'hits',sum(len(x['hits']) for x in out))
elif sys.argv[1]=='registryread':
 for r in json.loads((L/'registry-screen.json').read_text())['records']:
  print(r['path'])
  for h in r['hits']:
   s=h.get('path','') if isinstance(h,dict) else h
   if re.search('Legendre|Pouso|Segura|Kohler|Lucardesi|Quadrature|Petras',s,re.I):print(s)
elif sys.argv[1]=='readjson':
 for p in sys.argv[2:]:
  j=json.loads(Path(p).read_bytes());print(p, type(j),list(j)[:30] if isinstance(j,dict) else len(j))
elif sys.argv[1]=='pool':
 p=L.parent/'pi-analysis-r1/sources/open-posts.json';j=json.loads(p.read_bytes());items=j.get('items',j.get('posts',j.get('data',[]))) if isinstance(j,dict) else j
 for r in items:
  if re.search('entropy|log-concav|geometr|convex|probabili|Bessel|complete.monot|inequal',json.dumps(r),re.I):print(r.get('number'),r.get('title'),r.get('first_stated_year_source_url'),r.get('excerpt'))
