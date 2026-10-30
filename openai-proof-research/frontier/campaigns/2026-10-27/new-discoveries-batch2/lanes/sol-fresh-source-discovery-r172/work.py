import sys,json,re,hashlib,datetime,urllib.request,gzip
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='init':
 base=L.parent/'sol-fresh-source-discovery-r171/history-receipt.json';raw=base.read_bytes();known={x[0]:x[1:] for x in json.loads(raw)['records']};paths=set(known)
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','DECISION.md']:
    if (d/n).is_file():paths.add(str((d/n).relative_to(R)))
 # Explicitly retain originals r111--113, independent of inherited qualification.
 for k in [111,112,113]:
  for d in L.parent.glob('*r'+str(k)):
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','DECISION.md']:
    if (d/n).is_file():paths.add(str((d/n).relative_to(R)))
 records=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();row=[p,sha(b),len(b)];records.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
 save('history-receipt.json',dict(utc=now(),base=str(base),base_sha256=sha(raw),records=records,changed=changed,missing=missing,policy='Inherited qualified original paths; immediate lane refresh; explicit r111-r113 retained. No new echo exclusions. Inherited coverage is bounded, not global.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 print('records',len(records),'changed',len(changed),'missing',len(missing))
elif sys.argv[1]=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');m=list(pat.finditer(s))
  if m:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,x.start()-120):x.end()+240] for x in m[:12]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits,indent=2)[:18000])
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);rec=dict(utc=now(),name=n,url=u)
  try:
   assert not any(x in u.lower() for x in ['github','codeload','sciencedirect','google.'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif sys.argv[1]=='text':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[]
  def handle_data(self,s):self.out.append(s)
 for n in sys.argv[2:]:
  p=P();p.feed((L/'sources'/n).read_text());(L/'sources'/(n+'.txt')).write_text(' '.join(p.out))
elif sys.argv[1]=='registry':
 pat=re.compile(sys.argv[2],re.I);rows=[]
 for rel in ['sol-fresh-source-discovery-r171/registry-original-screen.json','sol-fresh-source-discovery-r169/registry-screen.json']:
  p=L.parent/rel;j=json.loads(p.read_text());rs=j if isinstance(j,list) else j['records']
  for r in rs:
   p=Path(r['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode();hits=[v for v in s.splitlines() if pat.search(v)]
   rows.append(dict(path=str(p),sha256=sha(b),bytes=len(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),pattern=pat.pattern,records=rows,limits='Saved actual catalogues/trees only; not current clearance or body clearance. Historical caps and missing merges parked.'))
 print([(r['path'],len(r['hits'])) for r in rows])
elif sys.argv[1]=='prepare':
 import tarfile,subprocess
 with tarfile.open(L/'sources/rs-source.tar') as t:
  for m in t.getmembers():
   if m.isfile() and m.name.endswith(('.tex','.bbl')):
    b=t.extractfile(m).read();(L/'sources'/Path(m.name).name).write_bytes(b);print(m.name,len(b))
 subprocess.run(['pdftotext','-layout',str(L/'sources/monomial.pdf'),str(L/'sources/monomial.txt')],check=True)
 for n in ['history-receipt.json','history-qualification.json']:
  p=L.parent/('sol-fresh-source-discovery-r171' if n=='history-receipt.json' else 'sol-fresh-source-discovery-r168')/n
  (L/('inherited-'+n)).write_bytes(p.read_bytes())
 rows=[];pat=re.compile(r'2610[.-]37522|subpacketization|cross.ratio|jmsc|few.variables|tiny.squares|1801[.-]07672',re.I)
 for r in json.loads((L/'registry-screen.json').read_text())['records']:
  p=Path(r['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  try:
   j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else []
   hits=[x for x in items if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[x for x in s.splitlines() if pat.search(x.split('\t')[-1])]
  rows.append(dict(path=str(p),sha256=sha(b),hits=hits))
 save('registry-path-screen.json',dict(utc=now(),pattern=pat.pattern,records=rows,limits='Path-only saved snapshots. First raw-line screen preserved with hash false positives; not body/current/global clearance.'))
 print('registry path hits',[(r['path'],r['hits']) for r in rows])
