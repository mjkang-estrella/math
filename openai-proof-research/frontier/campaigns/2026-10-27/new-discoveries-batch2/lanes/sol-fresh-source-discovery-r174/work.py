import sys,json,re,hashlib,datetime,urllib.request,gzip,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 base=L.parent/'sol-fresh-source-discovery-r172/history-receipt.json'; raw=base.read_bytes(); known={r[0]:r[1:] for r in json.loads(raw)['records']}; paths=set(known)
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','REVIEW.md','DECISION.md']:
    if (d/n).is_file():paths.add(str((d/n).relative_to(R)))
 rows=[]; changed=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():raise RuntimeError('missing inherited '+p)
  b=f.read_bytes();row=[p,sha(b),len(b)];rows.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
 save('history-receipt.json',dict(utc=now(),base=str(base),base_sha256=sha(raw),records=rows,changed=changed,policy='r172 qualified ORIGINAL index retained, immediate original lane documents refreshed; no new exclusions; bounded coverage'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 for n in ['inherited-history-qualification.json','inherited-history-receipt.json']:(L/n).write_bytes((base.parent/n).read_bytes())
 print('records',len(rows),'changed',len(changed),'r111-113',[(k,sum(('r'+str(k)+'/') in r[0] for r in rows)) for k in [111,112,113]])
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace'); ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+180] for m in ms[:8]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:16000])
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1); rec=dict(utc=now(),url=u,name=n)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='text':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[]
  def handle_data(self,s):self.out.append(s)
 for n in sys.argv[2:]:
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
  else:
   p=P();p.feed((L/'sources'/n).read_text());(L/'sources'/(n+'.txt')).write_text(' '.join(p.out))
elif mode=='catalogues':
 pat=re.compile(sys.argv[2],re.I); rows=[]
 for item in json.loads((L.parent/'sol-fresh-source-discovery-r172/registry-screen.json').read_text())['records']:
  p=Path(item['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode(); rows.append(dict(path=str(p),sha256=sha(b),hits=[x for x in s.splitlines() if pat.search(x)]))
 for p in [R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']:
  b=p.read_bytes();rows.append(dict(path=str(p),sha256=sha(b),hits=[x for x in b.decode().splitlines() if pat.search(x)]))
 save('catalogue-screen.json',dict(utc=now(),pattern=pat.pattern,records=rows,limits='Cached catalogue coverage only; live denied routes not retried. Not worldwide clearance.'));print([(r['path'],len(r['hits'])) for r in rows])
elif mode=='paths':
 pat=re.compile(sys.argv[2],re.I);rows=[]
 for item in json.loads((L/'catalogue-screen.json').read_text())['records']:
  p=Path(item['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  try:
   j=json.loads(s)
   if isinstance(j,dict) and 'tree' in j:hits=[r for r in j['tree'] if pat.search(r.get('path',''))]
   else:hits=[s[max(0,m.start()-120):m.end()+250] for m in list(pat.finditer(s))[:15]]
  except json.JSONDecodeError:hits=[r for r in s.splitlines() if pat.search(r.split('\t')[-1])]
  rows.append(dict(path=str(p),sha256=sha(b),hits=hits))
 save('registry-path-screen.json',dict(utc=now(),pattern=pat.pattern,records=rows));print(json.dumps(rows,indent=2)[:22000])
elif mode=='archive':
 base=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
 names=['Problems/koprowski-lewis-2026-conjecture-3-1-hypermatrix-count.md','docs/develop/theory/KOPROWSKI_LEWIS_COUPLED_DIGIT_BIJECTION.md','Library/Combinatorics/koprowski2026enumeration.md','D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.lean']
 rows=[]
 for i,n in enumerate(names):
  p=base/n;b=p.read_bytes();dest='sources/public-companion-'+str(i)+p.suffix;(L/dest).write_bytes(b);rows.append(dict(original=str(p),copy=dest,sha256=sha(b),bytes=len(b),role='cached public body; acquisition chronology inherited from original cache, not new network evidence'))
 save('public-body-provenance.json',dict(utc=now(),records=rows))
 save('source-hashes.json',[dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted((L/'sources').iterdir()) if p.is_file()])
