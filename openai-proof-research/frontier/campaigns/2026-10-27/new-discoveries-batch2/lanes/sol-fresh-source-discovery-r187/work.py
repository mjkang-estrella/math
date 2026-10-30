from pathlib import Path
import sys,json,hashlib,datetime,re,urllib.request,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,v):(L/n).write_text(json.dumps(v,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 known={};bases=[]
 for k in [170,178,181,182,183,184]:
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
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,qualification='Retain inherited qualified originals including r111–113; no echo exclusion.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 inv=[]
 for k in [170,178,181,182,183,184]:
  for n in ['http.jsonl','failures.json','inherited-access.json']:
   p=L.parent/f'sol-fresh-source-discovery-r{k}'/n
   if p.exists():
    b=p.read_bytes();inv.append(dict(path=str(p),sha256=sha(b),body=b.decode(errors='replace')))
 save('inherited-access.json',inv)
 print(len(rows),len(changed),len(missing))
elif mode=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-120):m.end()+220] for m in ms[:4]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits,indent=2)[:22000])
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 denied=(L/'inherited-access.json').read_text()
 for a in sys.argv[2:]:
  n,u=a.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   assert not any(v in u.lower() for v in ['github','codeload','sciencedirect','google.','ieeexplore','openreview','d-nb.info','arxiv.org/search'])
   assert u not in denied,'Inherited URL; inspect rather than retry'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=20) as f:
    b=f.read(10000001);assert len(b)<=10000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif mode=='extract':
 for p in (L/'sources').glob('*.pdf'):
  if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
elif mode=='search':
 import urllib.parse,xml.etree.ElementTree as ET
 (L/'sources').mkdir(exist_ok=True)
 for i,q in enumerate(sys.argv[2:]):
  u='https://www.bing.com/search?format=rss&q='+urllib.parse.quote(q);r=dict(utc=now(),query=q,url=u)
  try:
   with urllib.request.urlopen(u,timeout=18) as f:b=f.read(500000)
   n='search-'+sha(q.encode())[:12]+'.xml';(L/'sources'/n).write_bytes(b);r.update(file=n,sha256=sha(b))
   root=ET.fromstring(b);r['items']=[dict(title=x.findtext('title'),url=x.findtext('link'),description=x.findtext('description')) for x in root.findall('.//item')]
  except Exception as e:r['error']=str(e)
  with (L/'search.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r))
