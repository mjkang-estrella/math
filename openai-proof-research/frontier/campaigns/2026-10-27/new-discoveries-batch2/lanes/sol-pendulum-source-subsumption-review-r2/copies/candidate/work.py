import sys,json,hashlib,datetime,urllib.request,re,os
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),name=n,url=u)
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'source-research/1.0'}),timeout=30) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif sys.argv[1]=='history':
 known={};bases=[]
 for r in [157,159,162,164]:
  p=L.parent/f'sol-fresh-source-discovery-r{r}'/('history-supplement.json' if r==162 else 'history-receipt.json');b=p.read_bytes();j=json.loads(b);bases.append([str(p),sha(b)])
  for k in ['records','additional_records']:
   for p,h,z in j.get(k,[]):known[p]=h
 q=json.loads((L.parent/'sol-fresh-source-discovery-r159/history-qualification.json').read_text());excluded={x['path'] for x in q['excluded_generated_echoes']}
 paths=set(known)-excluded
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','context','core','reopened','sources','output','replays','frozen'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str((Path(root)/n).relative_to(R)))
 pat=re.compile(sys.argv[2],re.I);records=[];changed=[];hits=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
  if pat.search(b.decode(errors='replace')):
   dest='sources/history-'+h+'.txt';(L/dest).write_bytes(b);hits.append([p,h,dest])
 save('history-receipt.json',dict(utc=now(),bases=bases,records=records,changed_or_new=changed,hits=hits,pattern=pat.pattern,role_exclusions=sorted(excluded),original_r111_r113=[p for p,h,z in records if re.search('/sol-fresh-source-discovery-r11[123]/',p)],limit='Inherited original-role inventories plus changed/new original scan; no arbitrary round cutoff.'))
 print('records',len(records),'changed',len(changed),'hits',len(hits));print('\n'.join(x[0] for x in hits))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
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
  print(n,s[:2500])
  for m in re.finditer(r'Conjecture',s):print(s[max(0,m.start()-300):m.end()+1200])
elif sys.argv[1]=='list':
 j=json.loads((L/'sources'/sys.argv[2]).read_text());print(str(j)[:500] if 'items' not in j else '\n'.join(str(x)[:1800] for x in j['items']))
