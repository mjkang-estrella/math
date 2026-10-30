import sys,json,hashlib,re,datetime,urllib.request,subprocess,gzip
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
mode=sys.argv[1]
if mode=='context':
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n,[(a.get('number'),a.get('title')) for a in j.get('accepted',[])],list(j))
  else:print(n,b.decode()[:18000])
elif mode=='scan':
 pat=re.compile(sys.argv[2],re.I);known={};baselines=[]
 for lane,n in [('r147','history-receipt.json'),('r148','history-initial.json'),('r149','history-leaf.json')]:
  p=L.parent/('sol-fresh-source-discovery-'+lane)/n;j=json.loads(p.read_bytes());baselines.append([str(p),sha(p.read_bytes())])
  if 'records' in j:known.update({p:h for p,h,z in j['records']})
  else:known.update({p:h for h,ps in j['aliases'].items() for p in ps})
 roles=re.compile(r'^(SUMMARY|discovery|PROOF|review|DECISION)[^/]*\.(md|txt)$',re.I)
 echo=re.compile(r'/(extracted[^/]*|rebuild[^/]*|replay[^/]*|packet|inputs|evidence|history|review-core|core|source-copy|verification|private|context|build|output|payload)/',re.I)
 known={p:h for p,h in known.items() if roles.match(Path(p).name) and not echo.search(p)}
 for d in (B/'lanes').iterdir():
  if not d.is_dir() or d==L:continue
  for f in d.iterdir():
   if f.is_file() and roles.match(f.name):known.setdefault(str(f.relative_to(R)),None)
 records=[];changed=[];missing=[];hits=[];seen=set()
 for p,h in sorted(known.items()):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();hh=sha(b);records.append([p,hh,len(b)])
  if h!=hh:changed.append(p)
  if hh in seen:continue
  seen.add(hh)
  if pat.search(b.decode(errors='replace')):
   q=L/'reopened'/sys.argv[3]/str(len(hits));q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);hits.append(dict(path=p,sha256=hh,copy=str(q.relative_to(L))))
 save('history-'+sys.argv[3]+'.json',dict(pattern=pat.pattern,baselines=baselines,records=records,changed=changed,missing=missing,hits=hits,full_bodies=True,cutoff=None,limits='Retained role indexes plus immediate batch original roles; no new recursive inventory; lexical only; nested new originals outside this frontier not enumerated.'))
 print(len(records),len(seen),'bodies',len(changed),'changed',len(hits),'hits');print(json.dumps(hits))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  print(n,[(m.start(),(L/('context-'+n)).read_text()[max(0,m.start()-180):m.end()+250]) for m in pat.finditer((L/('context-'+n)).read_text())])
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif mode=='text':
 for n in sys.argv[2:]:print(subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True))
elif mode=='registry':
 pat=re.compile(r'Kazemi|dominator|total.?dominat|hypercube|cm[.]2025[.]102',re.I);out=[]
 for n in ['omega-tree.txt.gz','openai-tree.txt.gz']:
  p=L.parent/'root-edge-irregulator-final-freeze-r1'/n;hits=[];count=0
  with gzip.open(p,'rt') as f:
   for line in f:
    count+=1
    if pat.search(line):hits.append(line.strip())
  out.append(dict(path=str(p),sha256=sha(p.read_bytes()),lines=count,hits=hits))
 for lane,n in [('r138','sources/omega-compare.json'),('r141','sources/omega-fixed-delta.json')]:
  p=L.parent/('sol-fresh-source-discovery-'+lane)/n;j=json.loads(p.read_bytes());out.append(dict(path=str(p),sha256=sha(p.read_bytes()),base=j['base_commit']['sha'],merge_base=j['merge_base_commit']['sha'],files=len(j['files']),capped=len(j['files'])==300,hits=[x['filename'] for x in j['files'] if pat.search(json.dumps(x))]))
 save('registry-screen.json',out);print(json.dumps(out))
elif mode=='library':
 p=L/'sources/omega-library.json';j=json.loads(p.read_bytes());pat=re.compile(r'Kazemi|dominator|total.?dominat|hypercube|cm[.]2025[.]102',re.I)
 out=dict(utc=now(),path=str(p),sha256=sha(p.read_bytes()),truncated=j.get('truncated'),entries=len(j['tree']),hits=[x for x in j['tree'] if pat.search(x['path'])],limits='Complete fixed-head Library path walk only, not semantic clearance of registry. Both comparison intervals remain capped300.')
 save('registry-library-screen.json',out);print(json.dumps(out))
