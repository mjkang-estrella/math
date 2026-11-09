import os,resource,json,hashlib,datetime,concurrent.futures,urllib.request,subprocess,re,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).parent;s=p/'sources';s.mkdir(exist_ok=True)
jobs=[('https://arxiv.org/pdf/1008.2134','ayyer-strehl'),('https://muroran-it.repo.nii.ac.jp/record/8894/files/JAA_14-4.pdf','koda-sato-takegahara'),('https://arxiv.org/pdf/1004.3435','qc-spectrum'),('https://math.colgate.edu/~integers/n42/n42.pdf','goff-journal'),('https://arxiv.org/pdf/0903.5073','fischer-romik'),('https://danromik.com/resources/papers/squareice-revised.pdf','karklinsky-romik-journal'),('https://par.nsf.gov/servlets/purl/10431682','stack-queue-journal'),('https://www.trureturing.org/research/','registry-current'),('https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/master/data/projects.yml','projects-current')]
def fetch(job):
 url,name=job;dest=s/(name+'.pdf');r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=8) as f:b=f.read(12_000_000);r.update(status=f.status,final_url=f.url)
  dest.write_bytes(b);r.update(path=str(dest),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(dest),str(s/(name+'.txt'))],timeout=12,check=True)
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rec=list(ex.map(fetch,jobs))
(s/'extra-receipts.json').write_text(json.dumps(rec,indent=2)+'\n');print('PDF jobs',len(jobs),'errors',[r for r in rec if 'error' in r])
