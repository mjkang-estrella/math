import sys,json,re,hashlib,datetime,urllib.request,subprocess,gzip
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 known={};bases=[]
 for k in [170,178,180,181,182,183]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json';b=p.read_bytes();bases.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
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
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,policy='Original union with changed-file refresh; no new echo exclusions.'))
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 for k,n in [(183,'inherited-history-qualification.json'),(182,'original-copy-provenance.json'),(181,'failures.json'),(181,'source-lead-screen.json'),(178,'retained-originals.json')]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}'/n;(L/f'inherited-r{k}-{n}').write_bytes(p.read_bytes())
 print('records',len(rows),'changed',len(changed),'missing',len(missing),'r111-113',[(k,sum(f'r{k}/' in r[0] for r in rows)) for k in [111,112,113]])
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+230] for m in ms[:6]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:22000])
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),url=u,name=n)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.','ieeexplore','openreview','d-nb.info','ssrn'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='text':
 for n in sys.argv[2:]:subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
elif mode=='registry':
 pat=re.compile(r'25041|15[./]1[./]105|Lokshtanov|CountingGraphs|VertexCover|TriangleFree|Triangle.Free.Count',re.I);rows=[]
 for rec in json.loads((L.parent/'sol-fresh-source-discovery-r183/registry-screen.json').read_text())['records']:
  p=Path(rec['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  try:j=json.loads(s);hits=[x for x in j.get('tree',[]) if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[line[:1200] for line in s.splitlines() if pat.search(line)]
  rows.append(dict(path=str(p),sha256=sha(b),bytes=len(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),records=rows,pattern=pat.pattern,limits='Inherited actual bodies/catalogues only. Current HEADs, capped intervals, missing merge trees PARKED; no reconstruction or denied routes. Not novelty clearance.'))
 print([(r['path'],len(r['hits'])) for r in rows])
elif mode=='context':
 j=json.loads((L/'context-ledger.json').read_text());p=json.loads((L/'context-prior-campaign-context.json').read_text())
 save('context-read-receipt.json',dict(utc=now(),ledger_keys=list(j),prior_keys=list(p),accepted=[x.get('title') for x in j['accepted']],counts=[j['accepted_count'],j['total_accepted_count'],j['next_global_outcome_number']]))
 print((L/'context-read-receipt.json').read_text())
elif mode=='copies':
 rows=[];drift=[];(L/'originals').mkdir(exist_ok=True)
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  b=(R/p).read_bytes();dest='originals/'+sha(p.encode())[:20]+'-'+Path(p).name;(L/dest).write_bytes(b)
  rows.append(dict(original=p,copy=dest,sha256=sha(b),bytes=len(b)))
  if sha(b)!=h:drift.append(p)
 save('original-copy-provenance.json',dict(utc=now(),records=rows,drift_since_early_screen=drift,policy='All qualified records retained, including copies and older r111-113 originals. No echo exclusions.'))
 root=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing/Blueprint/D5/S3/Combinatorics/Graph'
 rs=[]
 for n in ['StarFormingTriangleFreeRefutation.md','Walks/DenseTriangleFreeConfigurations.md']:
  p=root/n;b=p.read_bytes();dest='sources/cached-'+p.name;(L/dest).write_bytes(b);rs.append(dict(original=str(p),copy=dest,sha256=sha(b),git_blob_sha1=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()))
 save('cached-body-receipts.json',dict(utc=now(),records=rs,limits='Cached public proof bodies, no current-head claim.'))
 (L/'inherited-r181-http.jsonl').write_bytes((L.parent/'sol-fresh-source-discovery-r181/http.jsonl').read_bytes())
 print('copies',len(rows),'drift',drift,'cached',rs)
