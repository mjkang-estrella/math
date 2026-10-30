import json, hashlib, datetime, sys, os, re, urllib.request, subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
if sys.argv[1]=='history':
 base=L.parent/'sol-fresh-source-discovery-r159/history-receipt.json'; qual=L.parent/'sol-fresh-source-discovery-r159/history-qualification.json'
 j=json.loads(base.read_bytes()); q=json.loads(qual.read_bytes()); excluded={x['path'] for x in q['excluded_generated_echoes']}
 known={p:h for p,h,z in j['records'] if p not in excluded}; paths=set(known)
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','context','reopened','sources','output','replays','frozen','tamper-controls','baseline-copy','author-copy'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str((Path(root)/n).relative_to(R)))
 records=[]; changed=[]; hits=[]; pat=re.compile(sys.argv[2],re.I)
 for p in sorted(paths-excluded):
  f=R/p
  if not f.is_file():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
  if pat.search(b.decode(errors='replace')):
   dest='sources/history-'+h+'.txt';(L/dest).write_bytes(b);hits.append(dict(path=p,sha256=h,copy=dest))
 save('history-receipt.json',dict(utc=now(),base=str(base),base_sha256=sha(base.read_bytes()),qualification_sha256=sha(qual.read_bytes()),records=records,changed_or_new=changed,pattern=pat.pattern,hits=hits,excluded_generated_by_role=q['excluded_generated_echoes'],cutoff=None,r111_r113=[p for p,h,z in records if re.search('/sol-fresh-source-discovery-r11[123]/',p)]))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 print(json.dumps(dict(records=len(records),changed=len(changed),hits=hits),indent=2))
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='clean':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[];self.skip=0
  def handle_starttag(self,t,a):
   if t in ['math','script','style']:
    if t=='math' and not self.skip:self.out.append(dict(a).get('alttext',''))
    self.skip+=1
   if t in ['p','h1','h2','h3','h4']:self.out.append('\n')
  def handle_endtag(self,t):
   if t in ['math','script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,s):
   if not self.skip:self.out.append(s)
 for n in sys.argv[2:]:
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
  else:
   p=P();p.feed((L/'sources'/n).read_text());(L/'sources'/(n+'.txt')).write_text(re.sub(r'[^\S\n]+',' ',' '.join(p.out)))
