import sys, json, hashlib, datetime, re, urllib.request, os
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b): return hashlib.sha256(b).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j): (L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
mode=sys.argv[1]
if mode=='registry':
 import gzip
 pat=re.compile(r'irregular|bastien|khormali|dovzhen|filuta|filiuta|lukashenko|mikhalev|delta.?complement',re.I); out=[]
 for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/sources/omega-fixed-delta.json']:
  p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  if p.suffix=='.json':
   j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))]
  else:paths=[x.split('\t')[-1] for x in s.splitlines()]
  hits=[x for x in paths if pat.search(x)];out.append(dict(path=str(p),sha256=sha(b),hits=hits))
 heads={n:json.loads((L/'sources'/(n+'-head.json')).read_bytes())['sha'] for n in ['omega','openai']}
 save('registry-screen.json',dict(utc=now(),records=out,current_heads=heads,fixed={'omega':'490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c','openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'},limits=['Two inherited capped300 comparisons do not clear absence','Lexical path checks do not clear semantic absence','No full new head inventory claimed']))
 print(json.dumps(dict(heads=heads,records=out),indent=2))
if mode=='clean':
 from html.parser import HTMLParser
 import subprocess
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[];self.skip=0
  def handle_starttag(self,t,a):
   if t in ['math','script','style']:
    if t=='math' and not self.skip:self.out.append(dict(a).get('alttext',''))
    self.skip+=1
   if t in ['p','h1','h2','h3','h4'] and not self.skip:self.out.append('\n')
  def handle_endtag(self,t):
   if t in ['math','script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,s):
   if not self.skip:self.out.append(s)
 for n in sys.argv[2:]:
  if n.endswith('.pdf'): subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
  else:
   p=P();p.feed((L/'sources'/n).read_text());(L/'sources'/(n+'.txt')).write_text(re.sub(r'[^\S\n]+',' ',' '.join(p.out)))
if mode=='history':
 base=L.parent/'sol-fresh-source-discovery-r156/history-receipt.json'; j=json.loads(base.read_bytes()); known={p:h for p,h,z in j['records']}; paths=set(known)
 # Refresh original scientific roles, excluding generated roles, never an entire lane.
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context','core','reopened','sources','output','replays','frozen'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}: paths.add(str((Path(root)/n).relative_to(R)))
 records=[]; changed=[]; hits=[]; pat=re.compile(sys.argv[2],re.I)
 for p in sorted(paths):
  if any(x in p.split('/') for x in skip): continue
  f=R/p
  if not f.is_file(): continue
  b=f.read_bytes(); h=sha(b); records.append([p,h,len(b)])
  if known.get(p)!=h: changed.append([p,h,len(b)])
  if pat.search(b.decode(errors='replace')):
   dest='sources/history-'+h+'.txt'; (L/dest).write_bytes(b); hits.append(dict(path=p,sha256=h,copy=dest))
 save('history-receipt.json',dict(utc=now(),baseline=str(base),baseline_sha256=sha(base.read_bytes()),records=records,changed_or_new=changed,pattern=pat.pattern,hits=hits,cutoff=None,original_r111_r113=[p for p,h,z in records if re.search('/sol-fresh-source-discovery-r11[123]/',p)]))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']: (L/('context-'+n)).write_bytes((B/n).read_bytes())
 print('originals',len(records),'changed',len(changed),'hits',json.dumps(hits))
elif mode=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1); rec=dict(utc=now(),name=n,url=u)
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001); assert len(b)<=12000000; (L/'sources'/n).write_bytes(b); rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e: rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
