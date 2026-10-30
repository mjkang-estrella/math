import sys,json,re,hashlib,datetime,urllib.request,subprocess,gzip
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 known={};bases=[]
 for k in [170,172,173,174]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json';b=p.read_bytes();bases.append([str(p),sha(b)])
  known.update({r[0]:r[1:] for r in json.loads(b)['records']})
 paths=set(known)
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','REVIEW.md','DECISION.md']:
    if (d/n).is_file():paths.add(str((d/n).relative_to(R)))
 rows=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();row=[p,sha(b),len(b)];rows.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,policy='Union of r170/172/173/174 qualified originals, immediate original refresh, no new exclusions; bounded inherited coverage.'))
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 p=L.parent/'sol-fresh-source-discovery-r174/inherited-history-qualification.json';(L/'inherited-history-qualification.json').write_bytes(p.read_bytes())
 print('records',len(rows),'changed',len(changed),'missing',len(missing),'r111-113',sum(any('r'+str(k)+'/' in r[0] for k in [111,112,113]) for r in rows))
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+220] for m in ms[:8]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:19000])
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),url=u,name=n)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='text':
 for n in sys.argv[2:]:subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
elif mode=='registry':
 pat=re.compile('karapetyan|2503[.-]22421|2511[.-]22346|switching.?rook|rook.?polynomial|parallelogram.?polyomino',re.I);rows=[]
 j=json.loads((L.parent/'sol-fresh-source-discovery-r172/registry-screen.json').read_text())
 for rec in j['records']:
  p=Path(rec['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  try:
   tree=json.loads(s);hits=[x for x in tree.get('tree',[]) if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[line for line in s.splitlines() if pat.search(line)]
  rows.append(dict(path=str(p),sha256=sha(b),bytes=len(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),records=rows,limits='Cached bounded catalogues only; no live/current or historical clearance. Denied routes not retried; missing merge bodies PARKED.'))
 print(json.dumps(rows,indent=2)[:15000])
