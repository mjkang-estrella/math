import urllib.request,urllib.error,json,datetime,hashlib,pathlib,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
b=pathlib.Path(__file__).resolve().parent
jobs=[('prior-main.tex', 'https://raw.githubusercontent.com/ArtificialZeng/AI-Has-Taste/f3ae144b74f238f22c2b84b5283cb14ce912fd33/reproducible_source_code/BigWIN2/BW2-PR20260914-brugidou_positivity/source/manuscript/main.tex'), ('prior-problem.md', 'https://raw.githubusercontent.com/ArtificialZeng/AI-Has-Taste/f3ae144b74f238f22c2b84b5283cb14ce912fd33/reproducible_source_code/BigWIN2/BW2-PR20260914-brugidou_positivity/source/problem.md'), ('brugidou-abs.html', 'https://arxiv.org/abs/2306.15300'), ('tutte-abs.html', 'https://arxiv.org/abs/2509.20959')]
def fetch(job):
 n,u=job;r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as f:d=f.read(20000000);r['status']=f.status
  (b/'sources'/n).write_bytes(d);r.update(sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
 except Exception as e:r['error']=str(e)
 return r
receipts=list(concurrent.futures.ThreadPoolExecutor(5).map(fetch,jobs))
(b/'http-bodies.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
