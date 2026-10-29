import urllib.request,urllib.error,json,datetime,hashlib,pathlib,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
b=pathlib.Path(__file__).resolve().parent
jobs=[('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/65b7e4d804a45e6b255f6f0974bbda900855a3e6')]+[(n+'.tex','https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/'+q) for n,q in [('snaky','Snaky-in-21-Maker-moves-September-25-2026/build/introduction.tex'),('triangle','The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/build/introduction.tex'),('degree','Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026/build/sections/00-introduction.tex')]]
def fetch(job):
 n,u=job;r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as f:d=f.read(20000000);r['status']=f.status
  (b/'sources'/n).write_bytes(d);r.update(sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
 except Exception as e:r['error']=str(e)
 return r
receipts=list(concurrent.futures.ThreadPoolExecutor(5).map(fetch,jobs))
(b/'http-screen.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
