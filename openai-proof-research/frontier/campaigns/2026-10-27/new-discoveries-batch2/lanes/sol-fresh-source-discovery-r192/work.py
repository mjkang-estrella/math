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
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Source research'}),timeout=25) as f:
   b=f.read(12000001);assert len(b)<12000001;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
 except Exception as e:r['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r)
if sys.argv[1]=='init':
 known={};aliases=[]
 for k in [188,189,190]:
  d=L.parent/f'sol-fresh-source-discovery-r{k}'
  for n in ['SUMMARY.md','discovery.md','http.jsonl','failures.json','FAILURES.md','inherited-access.json','registry-screen.json']:
   p=d/n
   if p.exists():
    q=L/'context'/f'r{k}-{n}';q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
  p=d/'original-copy-provenance.json'
  if p.exists():
   rows=json.loads(p.read_text())
   if isinstance(rows,dict):rows=rows.get('records',rows.get('pairs',[]))
   for r in rows:
    if isinstance(r,dict):known[r['original']]=r.get('sha256')
    elif isinstance(r,list):known[str(R/r[0])]=r[2] if len(r)>2 else None
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('snapshot-'+n)).write_bytes((B/n).read_bytes())
 (L/'snapshot-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 # Discover direct records while pruning generated histories. Inherited records remain
 # coverage aliases; resolve only demonstrable same-hash suffix provenance.
 skip={'originals','copies','frozen','frozen-copy','scientific-copies','inputs','EXTRACTED','extracted','extracted-replay','primary-copies','node_modules','.git','context'}
 for root,ds,fs in os.walk(R/'frontier/campaigns'):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in ['summary.md','discovery.md','proof.md','review.md','decision.md']:known.setdefault(str(Path(root)/n),None)
 rows=[];missing=[];by_suffix={}
 for s,h in sorted(known.items()):
  p=Path(s)
  if not p.exists():missing.append(s);continue
  b=p.read_bytes();digest=sha(b)
  by_suffix.setdefault((p.name,digest),[]).append(p)
  rows.append(dict(original=s,sha256=digest,previous_sha256=h,changed=h!=digest,bytes=len(b)))
 canonical={}
 for r in rows:
  p=Path(r['original']);options=by_suffix[(p.name,r['sha256'])]
  # A copied suffix must contain the full actual campaign-relative path.
  matches=[q for q in options if q!=p and str(q.relative_to(R)) in str(p.relative_to(R)) and len(str(q))<len(str(p))]
  q=min(matches,key=lambda q:len(str(q))) if matches else p
  r['canonical_original']=str(q);r['provenance_basis']='identical bytes and embedded full original relative path' if matches else 'direct original; no inferred content-only deduplication'
  canonical[str(q)]=r['sha256']
 for s,h in canonical.items():
  p=Path(s);q=L/'originals'/p.relative_to(R);q.parent.mkdir(parents=True,exist_ok=True);b=p.read_bytes();assert sha(b)==h;q.write_bytes(b);assert sha(q.read_bytes())==h
 save('history-coverage.json',dict(utc=now(),records=rows,missing=missing,canonical_count=len(canonical),aliases=len(rows)-len(canonical),limits='Qualified records, not all history; provenance-only dedup. Retains r111–113.'))
 save('scientific-freeze.json',[dict(original=s,copy=str((L/'originals'/Path(s).relative_to(R)).relative_to(L)),sha256=h) for s,h in canonical.items()])
 print('coverage',len(rows),'canonical',len(canonical),'aliases',len(rows)-len(canonical),'missing',len(missing),'r111-113',sum(any(f'discovery-r{k}/' in s for k in [111,112,113]) for s in canonical))
elif sys.argv[1]=='fetch':
 for a in sys.argv[2:]:fetch(*a.split('=',1))
elif sys.argv[1]=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for r in json.loads((L/'scientific-freeze.json').read_text()):
  t=(L/r['copy']).read_text(errors='replace');m=list(pat.finditer(t))
  if m:hits.append(dict(original=r['original'],excerpts=[t[max(0,x.start()-80):x.end()+180] for x in m[:3]]))
 save(sys.argv[3],dict(pattern=pat.pattern,hits=hits,utc=now()));print(json.dumps(hits)[:18000])
elif sys.argv[1]=='extract':
 for p in (L/'sources').glob('*.pdf'):
  if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
