import pathlib,json,hashlib,urllib.request,datetime
L=pathlib.Path(__file__).resolve().parent;R=L.parents[5]
H=lambda b:hashlib.sha256(b).hexdigest()
hits=[]; bindings=[]
terms=['crazy knight','crazy knight’s','2311.09054','toroidal board','mella','pasotti']
paths=list((R/'sources/cache').rglob('*.tex'))+list(L.parent.glob('*/discovery.md'))+list(L.parent.glob('*/SUMMARY.md'))+list(L.parent.glob('*/SCOUTING.md'))
for p in paths:
 if p.is_relative_to(L) or p.stat().st_size>2000000:continue
 b=p.read_bytes();sha=H(b);s=b.decode(errors='replace'); ls=s.splitlines()
 found=[(i+1,line[:800]) for i,line in enumerate(ls) if any(t in line.lower() for t in terms)]
 assert H(p.read_bytes())==sha
 if found:
  bindings.append(dict(original=str(p),sha256=sha,bytes=len(b),mode='immutable-reference'))
  hits.append(dict(path=str(p),hits=found[:60]))
(L/'semantic-screen.json').write_text(json.dumps(dict(files_screened=len(paths),hits=hits),indent=2)+'\n')
(L/'screen-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
urls=['https://export.arxiv.org/api/query?search_query=all:%22crazy%20knight%22&start=0&max_results=30','https://arxiv.org/abs/2311.09054','https://ajc.maths.uq.edu.au/pdf/76/ajc_v76_p183.pdf']
access=[]
for i,url in enumerate(urls):
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
   b=f.read(3000000);rec.update(status=f.status,sha256=H(b),bytes=len(b),final_url=f.url)
  p=L/('live-'+str(i)+('.pdf' if b.startswith(b'%PDF') else '.txt'));p.write_bytes(b)
  assert H(p.read_bytes())==rec['sha256'];rec['copy']=p.name
 except Exception as e:rec['failure']=str(e)
 access.append(rec)
(L/'access.json').write_text(json.dumps(access,indent=2)+'\n')
print(json.dumps(dict(files_screened=len(paths),hit_files=len(hits),access=access),indent=2))
