import sys,json,re,hashlib,datetime,urllib.request,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 known={};bases=[]
 for k in [170,174,175,176]:
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
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,policy='Retained qualified original union; all immediate lane scientific originals refreshed; no new echo exclusions. Bounded inherited qualification, no path-absence clearance.'))
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 for k in [170,174,175,176]:
  for n in ['inherited-history-qualification.json','qualification-r170.json']:
   p=L.parent/f'sol-fresh-source-discovery-r{k}'/n
   if p.exists():(L/f'inherited-r{k}-{n}').write_bytes(p.read_bytes())
 print('records',len(rows),'changed',len(changed),'missing',len(missing),'r111-113',sum(any('r'+str(k)+'/' in r[0] for k in [111,112,113]) for r in rows))
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+220] for m in ms[:7]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:22000])
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
elif mode=='htmltext':
 from html.parser import HTMLParser
 class Reader(HTMLParser):
  def __init__(self):super().__init__();self.parts=[];self.skip=0
  def handle_starttag(self,tag,attrs):
   if tag in ['script','style']:self.skip+=1
  def handle_endtag(self,tag):
   if tag in ['script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,s):
   if not self.skip and s.strip():self.parts.append(s.strip())
 for n in sys.argv[2:]:
  p=Reader();p.feed((L/'sources'/n).read_text());(L/'sources'/(n+'.txt')).write_text('\n'.join(p.parts))
