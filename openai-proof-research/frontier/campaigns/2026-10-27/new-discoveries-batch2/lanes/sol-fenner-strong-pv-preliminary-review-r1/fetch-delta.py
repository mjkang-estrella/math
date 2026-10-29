import resource,signal,os,pathlib,json,urllib.request,hashlib,datetime
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,)*2);signal.alarm(45)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
p=pathlib.Path(__file__).parent
urls={'jin-original.pdf':'https://raw.githubusercontent.com/MColbrook/AIM/c1f79e312f2b7bae2636469c506376a873100691/research/solutions/629-extrapolation-discreteness/paper/extrapolation_discreteness.pdf','omega-delta.json':'https://api.github.com/repos/the-omega-institute/trureturing/compare/cf1a97c474c3a1c375593282e484a85561ae45e2...65b7e4d804a45e6b255f6f0974bbda900855a3e6','pinch.pdf':'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5D9748D45FF425B687F829AAD1B9AF67/S0305004100062587a.pdf/a-convexity.pdf'}
logs=[]
for n,u in urls.items():
 d={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research-review/1.0'}),timeout=10) as r:b=r.read(12000000);d.update(status=r.status,content_type=r.headers.get('Content-Type'))
  (p/'sources'/n).write_bytes(b);d.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:d['error']=str(e)
 logs.append(d);(p/'http-delta.json').write_text(json.dumps(logs,indent=2));print(n,d)
