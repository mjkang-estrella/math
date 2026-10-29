import urllib.request,json,hashlib,datetime,resource,signal
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(220)
D=Path(__file__).resolve().parent;head=json.loads((D/'live/heads.json').read_text()) if (D/'live/heads.json').exists() else json.loads((D/'heads.json').read_text());rows=[]
paths=['D5/S3/Axis/TraceMap/ContainerWitness.lean','D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.lean','Problems/condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence.md','D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition.lean','D5/S3/ConceptDynamics/Agency/MinimumInstalledReadout.lean']
items=[('omega-'+Path(p).name,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head['omega']['head']+'/'+p) for p in paths]
items += [('l-polyomino-chronology.json','https://api.github.com/repos/the-omega-institute/trureturing/commits?sha='+head['omega']['head']+'&path=D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.lean&per_page=100')]
for p in ['Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026/build/sections/01-introduction.tex','The-Kakeya-maximal-conjecture-in-three-dimensions-September-23-2026/build/sections/10-setup.tex']:
 items.append(('openai-'+p.split('/')[0]+'.tex','https://raw.githubusercontent.com/openai/math/'+head['openai']['head']+'/preprints/'+p))
for name,url in items:
 row=dict(url=url,started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'source-prior-review/1.0'}),timeout=15) as f:b=f.read(2*1024**2+1);row['status']=f.status
  if len(b)>2*1024**2:raise ValueError('body cap')
  (D/'live'/name).write_bytes(b);row.update(file='live/'+name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['error']=str(e)
 row['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();rows.append(row);(D/'body-http.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
