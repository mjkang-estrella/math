import sys,json,hashlib,datetime,urllib.request,re,os
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
mode=sys.argv[1]
if mode=='history':
 old=L.parent/'sol-fresh-source-discovery-r150/history-receipt.json'; j=json.loads(old.read_bytes()); known={p:h for p,h,z in j['records']}; paths=set(known)
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context','core','reopened','sources','output','replays'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str((Path(root)/n).relative_to(R)))
 records=[];changed=[];hits=[];pat=re.compile(sys.argv[2],re.I)
 for p in sorted(paths):
  if any(x in p.split('/') for x in skip):continue
  f=R/p
  if not f.exists():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
  if pat.search(b.decode(errors='replace')):
   hits.append(dict(path=p,sha256=h,bytes=len(b)));(L/'sources'/('history-'+h+'.txt')).write_bytes(b)
 save('history-receipt.json',dict(utc=now(),baseline=str(old),baseline_sha256=sha(old.read_bytes()),records=records,changed_or_new=changed,pattern=pat.pattern,hits=hits,cutoff=None,qualification='Inherited qualified original-role scope; full original bodies, no global output cutoff. Generated replay/source/context roles excluded, not whole scientific lanes. No workspace-wide semantic clearance.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
 print('records',len(records),'changed',len(changed),'hits',hits)
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);rec=dict(utc=now(),name=name,url=url)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=25) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12MB cap')
    (L/'sources'/name).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='registry':
 import gzip
 pat=re.compile(r'Toeplitz|Malik|Qureshi|Hamiltonicity|permutahedr',re.I);out=[]
 for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/sources/omega-fixed-delta.json']:
  p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  if p.suffix=='.json':
   j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))]
  else:paths=[x.split('\t')[-1] for x in s.splitlines()]
  hits=[x for x in paths if pat.search(x)];out.append(dict(path=str(p),sha256=sha(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),records=out,omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',gaps=['aa026->a19a capped300','a19a->490f capped300','lexical scope only; no full semantic absence clearance']))
 print(json.dumps(out,indent=2))
