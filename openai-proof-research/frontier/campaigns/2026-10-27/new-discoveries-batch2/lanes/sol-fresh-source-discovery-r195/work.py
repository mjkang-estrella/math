from pathlib import Path
import os,sys,json,hashlib,datetime,urllib.request,re,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]; R=B.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def fetch(n,u):
 (L/'sources').mkdir(exist_ok=True);r=dict(utc=now(),url=u,file=n)
 try:
  assert not any(x in u.lower() for x in ['github','codeload','sciencedirect','google.','crossref','export.arxiv','dblp','duckduckgo'])
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical source research'}),timeout=25) as f:
   b=f.read(10000001);assert len(b)<10000001;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
 except Exception as e:r['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r)
if sys.argv[1]=='init':
 old=json.loads((L.parent/'sol-fresh-source-discovery-r192/history-coverage.json').read_text())['records']
 known={r['original']:r['sha256'] for r in old}; skip={'originals','copies','frozen','frozen-copy','scientific-copies','inputs','extracted','extracted-replay','primary-copies','node_modules','.git','context','assigned-inputs','history','administrative','rebuild-extraction','fresh-source-replay','strict-replay'}
 for root,ds,fs in os.walk(R/'frontier/campaigns'):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in ['summary.md','discovery.md','proof.md','review.md','decision.md']:known.setdefault(str(Path(root)/n),None)
 rows=[]; groups={}
 for s,h in sorted(known.items()):
  p=Path(s)
  if not p.exists():continue
  b=p.read_bytes();r=dict(original=s,sha256=sha(b),previous=h,changed=h!=sha(b));rows.append(r);groups.setdefault((p.name.lower(),r['sha256']),[]).append(p)
 canonical={};aliases=[]
 for r in rows:
  p=Path(r['original']); opts=groups[(p.name.lower(),r['sha256'])]
  # A generated copy must reproduce the enclosing original lane/directory suffix,
  # in addition to having identical bytes. Content equality alone never deduplicates.
  opts=[q for q in opts if q==p or ('/'+q.parent.name+'/'+q.name).lower() in str(p).lower() and len(str(q))<len(str(p))]
  q=min(opts,key=lambda q:len(str(q)));r['canonical']=str(q)
  if q!=p:aliases.append(r)
  canonical[str(q)]=r['sha256']
 freeze=[]
 for s,h in canonical.items():
  p=Path(s);q=L/'originals'/p.relative_to(R);q.parent.mkdir(parents=True,exist_ok=True);b=p.read_bytes();assert sha(b)==h;q.write_bytes(b);assert sha(q.read_bytes())==h
  freeze.append(dict(original=s,copy=str(q.relative_to(L)),sha256=h))
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('snapshot-'+n)).write_bytes((B/n).read_bytes())
 (L/'snapshot-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 for r in [189,191,192]:
  p=L.parent/f'sol-fresh-source-discovery-r{r}'
  for n in ['SUMMARY.md','discovery.md','FAILURES.md','inherited-access.json','http.jsonl','provenance.json','history-coverage.json']:
   if (p/n).exists():
    q=L/'context'/f'r{r}-{n}';q.parent.mkdir(exist_ok=True);q.write_bytes((p/n).read_bytes())
 save('history-coverage.json',dict(utc=now(),records=rows,aliases=aliases,canonical_count=len(canonical),limits='Bounded original refresh; same hash plus enclosing original directory/name provenance. Not exhaustive worldwide history.'))
 save('scientific-freeze.json',freeze)
 changed=[r for r in rows if r['changed'] and r['original']==r['canonical']];save('changed-records-read.json',changed)
 print('originals',len(freeze),'aliases',len(aliases),'changed',len(changed),'r111-113',sum(any(f'discovery-r{k}/' in s for k in [111,112,113]) for s in canonical))
 for r in changed:print(r['original'],Path(r['original']).read_text()[:2500])
elif sys.argv[1]=='fetch':
 for a in sys.argv[2:]:fetch(*a.split('=',1))
elif sys.argv[1]=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for r in json.loads((L/'scientific-freeze.json').read_text()):
  t=(L/r['copy']).read_text(errors='replace');m=list(pat.finditer(t))
  if m:hits.append(dict(original=r['original'],excerpts=[t[max(0,x.start()-90):x.end()+190] for x in m[:2]]))
 save(sys.argv[3],dict(pattern=pat.pattern,hits=hits,utc=now()));print(json.dumps(hits)[:18000])
elif sys.argv[1]=='extract':
 for p in (L/'sources').glob('*.pdf'):
  if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
