import sys,json,re,hashlib,datetime,urllib.request,subprocess,gzip
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='init':
 known={}; bases=[]
 for k in [170,173,174,175]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json'; b=p.read_bytes(); bases.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
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
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,limits='Qualified inherited originals retained; additions include echoes conservatively; no new exclusions or old-lane cutoff. Lexical coverage only.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  j=json.loads(b) if n.endswith('.json') else b.decode();print(n,len(b),list(j)[:12] if isinstance(j,dict) else j[:180])
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 for k,n in [(170,'history-qualification.json'),(173,'retained-originals.json'),(175,'qualification-r172.json')]: (L/f'qualification-r{k}.json').write_bytes((L.parent/f'sol-fresh-source-discovery-r{k}'/n).read_bytes())
 print('history',len(rows),'changed',len(changed),'missing',len(missing))
elif sys.argv[1]=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+240] for m in ms[:5]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits,indent=2)[:18000])
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   assert not any(v in u.lower() for v in ['github','codeload','sciencedirect','google.','ieeexplore','openreview'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='extract':
 for p in (L/'sources').glob('*.pdf'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 from html.parser import HTMLParser
 class P(HTMLParser):
  def __init__(self):super().__init__();self.out=[]
  def handle_data(self,s):self.out.append(s)
 for f in (L/'sources').glob('*.html'):
  p=P();p.feed(f.read_text());f.with_suffix('.html.txt').write_text('\n'.join(p.out))
elif sys.argv[1]=='registry':
 pat=re.compile(sys.argv[2],re.I);out=[]
 p=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
 for r in json.loads(p.read_text())['records']:
  f=Path(r['path']);b=f.read_bytes();s=gzip.decompress(b).decode() if f.suffix=='.gz' else b.decode()
  try:
   j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else [];hits=[x for x in items if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[x for x in s.splitlines() if pat.search(x.split('\t')[-1])]
  out.append(dict(path=str(f),sha256=sha(b),hits=hits))
 save(sys.argv[3] if len(sys.argv)>3 else 'registry-screen.json',dict(utc=now(),records=out,pattern=pat.pattern,limits='Cached names only; uninspected bodies and capped historical intervals HOLD/PARKED. No HEAD or denied retrieval retries.'))
 print(json.dumps(out,indent=2)[:18000])
elif sys.argv[1]=='copies':
 C=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'; rec=[]
 for sub in ['Blueprint/D5/S3/Analytic/KummerRatio/'+n+'.md' for n in ['Result','Comparison','Defs','Asymptotics','BetaAsymptotics','BetaIntegral','Series','Transform']]+['Blueprint/D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.md','Problems/nikolov-2023-snake-polynomial-chebyshev-expansion.md','Problems/karp-sitnik-2010-kummer-ratio-monotonicity.md']:
  p=C/sub;b=p.read_bytes();name='cached-'+sub.replace('/','--');(L/'sources'/name).write_bytes(b)
  rec.append(dict(original=str(p),copy='sources/'+name,sha256=sha(b),git_blob_sha1=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),public_url='https://github.com/the-omega-institute/trureturing/blob/f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada/'+sub))
 for name in ['radon-journal.html','radon-journal.txt','radon-v1.pdf','radon-v1.txt','radon-abs.html','white.txt']:
  p=L.parent/'sol-fresh-source-discovery-r47/sources'/name;b=p.read_bytes();(L/'sources'/('cached-'+name)).write_bytes(b);rec.append(dict(original=str(p),copy='sources/cached-'+name,sha256=sha(b)))
 p=C/'.git/logs/HEAD';b=p.read_bytes();(L/'cached-clone-log.txt').write_bytes(b)
 save('cached-copy-provenance.json',dict(utc=now(),records=rec,clone_head=(C/'.git/refs/heads/dev').read_text().strip(),clone_log='cached-clone-log.txt',limits='No git commands or network repository access; clone receipt establishes cached availability, not exact first-publication commit.'))
 save('scientific-freeze.json',dict(utc=now(),records=[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted((L/'sources').iterdir()) if p.is_file()],originals=[[r['original'],r['sha256']] for r in rec],exclusions=['Administrative live NEXT/ledger are context snapshots only.','Self/receipt files excluded from scientific claim freeze.']))
 print('copied',len(rec))
