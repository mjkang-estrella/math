from pathlib import Path
import sys,json,hashlib,datetime,os,re,urllib.request,urllib.error,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def bind(p,n):
 b=p.read_bytes();c=L/n;c.parent.mkdir(parents=True,exist_ok=True);c.write_bytes(b);assert sha(p.read_bytes())==sha(c.read_bytes())==sha(b)
 return [str(p),n,sha(b),len(b)]
mode=sys.argv[1]
if mode=='init':
 known={};bindings=[]
 for r in [189,191]:
  d=L.parent/f'sol-fresh-source-discovery-r{r}'
  bindings.append(bind(d/'history-receipt.json',f'assigned-inputs/r{r}-history.json'))
  known.update({p:[h,z] for p,h,z in json.loads((d/'history-receipt.json').read_text())['records']})
  for n in ['FAILURES.md','http.jsonl','inherited-access.json','provenance.json']:
   if (d/n).exists():bindings.append(bind(d/n,f'assigned-inputs/r{r}-{n}'))
 paths=set(known);names={'summary.md','discovery.md','proof.md','review.md','decision.md'}
 # Retain inherited aliases. Newly discovered records must be direct campaign/lane/candidate records.
 for root,ds,fs in os.walk(R/'frontier/campaigns'):
  ds[:]=[d for d in ds if d not in {'originals','inputs','copies','frozen','packet','source','sources','private','evidence','node_modules','.lake','.git','assigned-inputs','context','payload','verification','extracted'} and not d.startswith(('verification-','extracted-','replay','fresh-replay'))]
  if Path(root)==L:ds[:]=[];continue
  for n in fs:
   if n.lower() in names:paths.add(str((Path(root)/n).relative_to(R)))
 rows=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.exists():missing.append(p);continue
  b=f.read_bytes();h=sha(b);row=[p,h,len(b)];rows.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
  bindings.append(bind(f,'originals/'+sha(p.encode())[:20]+'-'+f.name))
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('snapshot-'+n)).write_bytes((B/n).read_bytes())
 bindings.append(bind(R/'AGENTS.md','assigned-inputs/ancestor-AGENTS.md'))
 save('input-bindings.json',bindings)
 save('history-receipt.json',dict(utc=now(),records=rows,changed=changed,missing=missing,qualification='Union of corrected r189/r191 indexes, refreshed originals; inherited aliases retained, no content-hash-only deduplication; no claim that paths equal unique investigations. New scan prunes generated trees.'))
 save('changed-records-read.json',[dict(path=p,sha256=h,body=(R/p).read_text()) for p,h,z in changed])
 print('records/changed/missing',len(rows),len(changed),len(missing));print('\n'.join(p for p,h,z in changed))
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 previous=(L/'http.jsonl').read_text() if (L/'http.jsonl').exists() else ''
 inherited=''.join(p.read_text(errors='replace') for p in (L/'assigned-inputs').glob('*') if 'http' in p.name or 'access' in p.name)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);rec=dict(utc=now(),name=n,url=u)
  try:
   assert not any(x in u.lower() for x in ['github','codeload','sciencedirect','google.','export.arxiv','dblp','crossref','ieeexplore'])
   assert u not in previous,'Previously attempted lane URL; no retry'
   if u in inherited:
    assert u=='https://lean.up.railway.app/api/data','Inherited URL; inspect rather than retry (only explicitly successful live registry catalog refresh permitted)'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=22) as f:
    b=f.read(12000001);assert len(b)<=12000000;rec.update(status=f.status,final_url=f.url)
   (L/'sources'/n).write_bytes(b);rec.update(sha256=sha(b),bytes=len(b))
  except Exception as e:
   rec['error']=repr(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read(500000);(L/'sources'/(n+'.error')).write_bytes(b);rec['error_sha256']=sha(b)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I);out=[]
 for p,c,h,z in json.loads((L/'input-bindings.json').read_text()):
  if not c.startswith('originals/'):continue
  s=(L/c).read_text(errors='replace');m=list(pat.finditer(s))
  if m:out.append(dict(path=p,sha256=h,excerpts=[s[max(0,x.start()-80):x.end()+180] for x in m[:3]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=out));print(json.dumps(out)[:22000])
elif mode=='text':
 for n in sys.argv[2:]:
  p=L/'sources'/n
  subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True)
