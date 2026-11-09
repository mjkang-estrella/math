import signal
signal.alarm(140)
import pathlib,urllib.request,datetime,hashlib,json,subprocess,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));L=pathlib.Path(__file__).resolve().parent
jobs=[('dong-arxiv.pdf','https://arxiv.org/pdf/1511.02692'),('exoo.pdf','https://arxiv.org/pdf/2307.07308'),('moore.pdf','https://arxiv.org/pdf/2512.09680'),('kolokolnikov-journal.pdf','https://www.mathstat.dal.ca/~tkolokol/papers/maxalg.pdf'),('babai-journal.html','https://doi.org/10.1016/j.disc.2025.114721'),('openai-CONTENTS.md','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md')]
def get(j):
 name,url=j;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read();r['status']=f.status;r['final_url']=f.url
  (L/name).write_bytes(b);r.update(path=name,sha256=hashlib.sha256(b).hexdigest())
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/name),str(L/(name[:-4]+'.txt'))],timeout=8,capture_output=True)
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,jobs):
  with (L/'source-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r['url'],r.get('status',r.get('error')))
