import sys,json,re,hashlib,datetime,urllib.request,subprocess,os,gzip
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='registry':
 pat=re.compile('Poisson|Poincare|Poincaré|Wasserstein|LogSobolev|Shenfeld|Rotem',re.I);out=[]
 p=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
 for r in json.loads(p.read_text())['records']:
  f=Path(r['path']);b=f.read_bytes();s=gzip.decompress(b).decode() if f.suffix=='.gz' else b.decode()
  try:
   j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else [];hits=[x for x in items if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[x for x in s.splitlines() if pat.search(x.split('\t')[-1])]
  out.append(dict(path=str(f),sha256=sha(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),records=out,pattern=pat.pattern,limits='Cached names only; current head and missing/capped intervals PARKED. No live novelty clearance; exact primary public proofs already force retirement.'))
 print('registry snapshots',len(out),'hits',sum(len(x['hits']) for x in out))
elif sys.argv[1]=='meta':
 for n in ['poisson-meta.json','rotem-meta.json']:
  j=json.loads((L/'sources'/n).read_text())['message'];j=j['items'][0] if 'items' in j else j
  print(n,json.dumps({k:j.get(k) for k in ['title','DOI','link','published','relation','URL','resource']},indent=2))
elif sys.argv[1]=='pool':
 p=L.parent/'pi-analysis-r1/sources/open-posts.json';j=json.loads(p.read_bytes());print(type(j),list(j)[:10] if isinstance(j,dict) else len(j))
 items=j.get('items',j.get('posts',j.get('data',[]))) if isinstance(j,dict) else j
 for r in items:
  if re.search('entropy|log-concav|geometr|convex|probabili|Bessel|complete.monot|inequal',json.dumps(r),re.I):print(r.get('number'),r.get('title'),r.get('first_stated_year_source_url'),r.get('excerpt'))
elif sys.argv[1]=='init':
 known={};bases=[]
 for k in [170,175,176,177,178]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json';b=p.read_bytes();bases.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
 paths=set(known)
 for p in R.rglob('*.md'):
  if L in p.parents:continue
  if p.name.lower() in ['summary.md','discovery.md','proof.md','review.md','decision.md']:paths.add(str(p.relative_to(R)))
 rows=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();r=[p,sha(b),len(b)];rows.append(r)
  if known.get(p)!=r[1:]:changed.append(r)
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,qualification='Inherited qualified originals retained, including r111–113; conservative copy overinclusion retained. No blanket path/date exclusions.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n, list(j) if isinstance(j,dict) else len(j))
   if n=='ledger.json':print('counts',{k:j.get(k) for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 print('history',len(rows),'changed',len(changed),'missing',len(missing))
elif sys.argv[1]=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+240] for m in ms[:4]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits,indent=2)[:16000])
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   assert not any(v in u.lower() for v in ['github','codeload','sciencedirect','google.','ieeexplore','openreview','d-nb.info'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='extract':
 for p in (L/'sources').glob('*.pdf'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[];self.skip=0
  def handle_starttag(self,t,a):
   if t in ['script','style']:self.skip+=1
  def handle_endtag(self,t):
   if t in ['script','style']:self.skip=max(0,self.skip-1)
  def handle_data(self,s):
   if not self.skip:self.out.append(s)
 for f in (L/'sources').glob('*.html'):
  p=P();p.feed(f.read_text());f.with_suffix('.html.txt').write_text('\n'.join(s.strip() for s in p.out if s.strip()))
