import os,sys,json,hashlib,datetime,re,urllib.request
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
if sys.argv[1]=='history':
 bases=['sol-fresh-source-discovery-r157/history-receipt.json','sol-fresh-source-discovery-r159/history-receipt.json','sol-fresh-source-discovery-r162/history-supplement.json']; known={}; receipts=[]
 for rel in bases:
  p=L.parent/rel;b=p.read_bytes();j=json.loads(b);receipts.append([str(p),sha(b)])
  for k in ['records','additional_records']:
   for p,h,z in j.get(k,[]):known[p]=h
 paths=set(known);skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context','core','reopened','sources','output','replays','frozen'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str((Path(root)/n).relative_to(R)))
 pat=re.compile(r'complete monotonicity of log.functions|s13324-025-01136|\b(?:Ma|Weigert|Hao Li|Matkowski)\b|2606[.]27260|even.order convexity|split (?:CIF|covariance intersection)|guaranteed fast implementation|nested Newton|jca2591|jca33018|Convexity of Generators|Mulholland|subadditivity.{0,80}convexity',re.I)
 records=[];hits=[];changed=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
  if pat.search(b.decode(errors='replace')):
   dest='sources/history-'+h+'.txt';(L/dest).write_bytes(b);hits.append([p,h,dest])
 save('history-receipt.json',dict(utc=now(),bases=receipts,records=records,changed_or_new=changed,pattern=pat.pattern,hits=hits,cutoff=None,original_r111_r113=[p for p,h,z in records if re.search('/sol-fresh-source-discovery-r11[123]/',p)]))
 print('records',len(records),'changed',len(changed),'hits',len(hits));print('\n'.join(x[0] for x in hits))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  print(n,len(b),sha(b))
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),name=n,url=u)
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif sys.argv[1]=='registry':
 import gzip
 pat=re.compile(r'split|covariance|fourth.?order|even.?order|nested.?newton|2606.?27260|log.?function|weigert|rouro',re.I);out=[]
 for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/sources/omega-fixed-delta.json','sol-fresh-source-discovery-r157/sources/omega-delta.json','sol-fresh-source-discovery-r157/sources/openai-delta.json']:
  p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  if p.suffix=='.json':
   j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))]
  else:paths=[x.split('\t')[-1] for x in s.splitlines()]
  hits=[x for x in paths if pat.search(x)];out.append(dict(path=str(p),sha256=sha(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),records=out,limits=['Inherited aa026->a19a and a19a->490f capped300 paths remain gaps','Path screen is not semantic absence clearance']))
 for r in out:print(r['path'],json.dumps(r['hits']))
elif sys.argv[1]=='clean':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[];self.skip=0
  def handle_starttag(self,t,a):
   if t in ['math','script','style']:
    if t=='math' and not self.skip:self.out.append(dict(a).get('alttext',''))
    self.skip+=1
   if t in ['p','h1','h2','h3','h4','div'] and not self.skip:self.out.append('\n')
  def handle_endtag(self,t):
   if t in ['math','script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,s):
   if not self.skip:self.out.append(s)
 for n in sys.argv[2:]:
  p=P();p.feed((L/'sources'/n).read_text());s=re.sub(r'[^\S\n]+',' ',' '.join(p.out));(L/'sources'/(n+'.txt')).write_text(s)
  for m in re.finditer(r'Conjecture|Author|Theorem|Ma,|Weigert|Nakao|Noack',s,re.I):print(n,s[max(0,m.start()-100):m.end()+700])
elif sys.argv[1]=='context':
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  s=(B/n).read_text()
  if n.endswith('.json'):
   j=json.loads(s);print(n, list(j));print(json.dumps({k:v for k,v in j.items() if not isinstance(v,(dict,list))},indent=2))
  else:print(s)
