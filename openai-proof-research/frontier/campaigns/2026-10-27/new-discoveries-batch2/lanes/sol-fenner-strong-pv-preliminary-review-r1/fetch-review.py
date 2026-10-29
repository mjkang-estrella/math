import os,resource,signal,json,pathlib,urllib.request,hashlib,datetime
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(55)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
p=pathlib.Path(__file__).parent;p.joinpath('sources').mkdir(exist_ok=True); logs=[]
urls={
'jin.pdf':'https://raw.githubusercontent.com/MColbrook/AIM/24edaadc6bb272737d8da0745c662c992db07b22/research/solutions/629-extrapolation-discreteness/paper/extrapolation_discreteness.pdf',
'aim-history.json':'https://api.github.com/repos/MColbrook/AIM/commits?path=research/solutions/629-extrapolation-discreteness/paper/extrapolation_discreteness.pdf&per_page=10',
'aim-head.json':'https://api.github.com/repos/MColbrook/AIM/commits/HEAD',
'campbell.html':'https://arxiv.org/html/2609.30771v1',
'clopen.html':'https://clopen.solutions/OP-00787/',
'pinch.html':'https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/aconvexity/5D9748D45FF425B687F829AAD1B9AF67',
'meyer.pdf':'https://www.numdam.org/item/ASENS_1970_4_3_1_75_0.pdf',
'omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD',
'count-head.json':'https://api.github.com/repos/suvrit/count-ex-machina/commits/HEAD'}
for n,u in urls.items():
 row={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research-review/1.0'}),timeout=8) as r: data=r.read(12*1024**2);row['status']=r.status
  (p/'sources'/n).write_bytes(data);row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:row['error']=str(e)
 logs.append(row);(p/'http-review.json').write_text(json.dumps(logs,indent=2));print(n,row.get('status',row.get('error')))
