import sys,os,json,hashlib,datetime,re,urllib.request,urllib.parse
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,j): (L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
if sys.argv[1]=='init':
 p=L.parent/'sol-fresh-source-discovery-r169/history-receipt.json'; raw=p.read_bytes(); j=json.loads(raw); known={x[0]:x[1:] for x in j['records']}
 paths=set(known)
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','DECISION.md']:
    if (d/n).is_file(): paths.add(str((d/n).relative_to(R)))
 records=[]; changed=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file(): continue
  b=f.read_bytes(); row=[p,sha(b),len(b)];records.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
 save('history-receipt.json',dict(utc=now(),base_sha256=sha(raw),records=records,changed=changed,policy='r168 qualified inherited paths plus immediate original lane reports; no recursive census, no date cutoff; counterpart qualification inherited separately'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  raw=(B/n).read_bytes();(L/('context-'+n)).write_bytes(raw)
  j=json.loads(raw) if n.endswith('.json') else None
  print(n,sha(raw), {k:j[k] for k in j if k not in ['accepted','rejected','screened','excluded','in_progress']} if j else raw[:1100].decode())
 print('records',len(records),'changed',len(changed))
elif sys.argv[1]=='audit':
 pat=re.compile(sys.argv[2],re.I);j=json.loads((L/'history-receipt.json').read_text());hits=[]
 for p,h,z in j['records']:
  b=(R/p).read_bytes(); s=b.decode(errors='replace');m=list(pat.finditer(s))
  if m: hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,x.start()-100):x.end()+250] for x in m[:8]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits,indent=2)[:23000])
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),name=n,url=u)
  try:
   assert not any(x in u.lower() for x in ['github','codeload','sciencedirect','google.'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e: rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif sys.argv[1]=='text':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[];self.skip=0
  def handle_starttag(self,t,a):
   if t in ['script','style']:self.skip+=1
  def handle_endtag(self,t):
   if t in ['script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,s):
   if not self.skip:self.out.append(s)
 for n in sys.argv[2:]:
  p=P();p.feed((L/'sources'/n).read_text());s=' '.join(p.out);(L/'sources'/(n+'.txt')).write_text(s);print(s[:26000])
