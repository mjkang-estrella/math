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
 for p,h,z in json.loads((L.parent/'sol-fresh-source-discovery-r153/history-delta.json').read_bytes())['changed_or_new']:known[p]=h
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context','core','reopened','sources','output','replays','frozen'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str((Path(root)/n).relative_to(R)))
 excluded=[];changed=[];records=[]
 for p in sorted(paths):
  if any(x in p.split('/') for x in skip):excluded.append(p);continue
  f=R/p
  if not f.exists():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
 save('history-delta.json',dict(utc=now(),baseline=str(old),baseline_sha256=sha(old.read_bytes()),changed_or_new=changed,excluded_echo_paths=excluded,retained_body_count=len(records),cutoff=None,qualification='Qualified original role scope inherited; entire original bodies scanned. Not entire workspace semantic clearance.'))
 pat=re.compile(sys.argv[2] if len(sys.argv)>2 else r'2511[.]03847|1102[.]5109|Stern.polynomial|Altizio|Dilcher.{0,30}Kidwai|Ulas.{0,15}Ulas|half.plane.{0,30}Stern|Zeros and irreducibility of Stern',re.I)
 hits=[]
 for p,h,z in records:
  b=(R/p).read_bytes()
  if pat.search(b.decode(errors='replace')):
   hits.append(dict(path=p,sha256=h,bytes=z));(L/'sources'/('history-'+h+'.txt')).write_bytes(b)
 save('history-query-'+sha(pat.pattern.encode())[:12]+'.json',dict(utc=now(),pattern=pat.pattern,hits=hits,full_body_count=len(records),cutoff=None,original_r111_r113=[p for p,h,z in records if re.search(r'/sol-fresh-source-discovery-r11[123]/',p)]))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n,[(a.get('number'),a.get('title')) for a in j.get('accepted',[])])
 print('changed/new',changed);print('hits',hits)
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
elif mode=='text':
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
  p=P();p.feed((L/'sources'/n).read_text());(L/'sources'/(n+'.txt')).write_text('\n'.join(p.out))
elif mode=='registry':
 import gzip
 pat=re.compile(r'Read.?Once|Factorial.*Divis|Divis.*Factorial|Lien.?Hung|21853500|Bhargava',re.I);records=[]
 for rel in ['sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/registry-delta.json']:
  p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  if p.suffix=='.json':
   j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))]
  else:paths=[x.split('\t')[-1] for x in s.splitlines()]
  hits=[x for x in paths if pat.search(x)]
  relevant=hits
  records.append(dict(path=str(p),sha256=sha(b),broad_match_count=len(hits),target_facing_hits=relevant,qualification='Lexical leads only; unread bodies do not establish exclusions'))
 save('registry-screen.json',dict(utc=now(),pattern=pat.pattern,records=records,omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',gaps=['aa026->a19a capped300','a19a->490f capped300','lexical paths only, no global semantic clearance; inherited cache chronology retained']))
 print('Registry screen saved; target-facing paths only retained.')
elif mode=='clean':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[];self.ignore=0
  def handle_starttag(self,t,a):
   if t in ['math','script','style']:
    if t=='math' and not self.ignore:self.out.append(dict(a).get('alttext',''))
    self.ignore+=1
   if t in ['p','h1','h2','h3','h4'] and not self.ignore:self.out.append('\n')
  def handle_endtag(self,t):
   if t in ['math','script','style']:self.ignore=max(0,self.ignore-1)
  def handle_data(self,s):
   if not self.ignore:self.out.append(s)
 for n in sys.argv[2:]:
  p=P();p.feed((L/'sources'/n).read_text());s=' '.join(p.out);s=re.sub(r'[^\S\n]+',' ',s);(L/'sources'/(n+'.clean.txt')).write_text(s)
