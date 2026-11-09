import signal
signal.alarm(140)
import pathlib,json,urllib.request,hashlib,datetime,concurrent.futures,subprocess,resource,re,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
jobs=[]
if sys.argv[1]=='versions':
 for p in L.glob('*.abs'):
  a=p.stem
  vs=set(re.findall('/abs/'+re.escape(a)+r'v(\d+)',p.read_text()))
  for v in sorted(vs,key=int):jobs.append((a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v))
else:
 jobs=[('openai-head.html','https://github.com/openai/math/commits/HEAD'),('omega-head.html','https://github.com/the-omega-institute/trureturing/commits/HEAD'),('pool-head.html','https://github.com/Vilin97/lean-pool/commits/HEAD'),('pool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml'),('dong.pdf','https://cdn.sciengine.com/doi/pdf/ece1e28617934dccb115b38c78e4783f'),('game-journal.pdf','https://dmtcs.episciences.org/3127/pdf'),('1412.1438.pdf','https://arxiv.org/pdf/1412.1438'),('2005.02797.pdf','https://arxiv.org/pdf/2005.02797')]
def get(job):
 name,url=job;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=12) as f:b=f.read();r['status']=f.status;r['final_url']=f.url
  (L/name).write_bytes(b);r.update(path=name,sha256=hashlib.sha256(b).hexdigest())
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/name),str(L/(name[:-4]+'.txt'))],timeout=8,capture_output=True)
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,jobs):
  with (L/'source-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r['url'],r.get('status',r.get('error')))
