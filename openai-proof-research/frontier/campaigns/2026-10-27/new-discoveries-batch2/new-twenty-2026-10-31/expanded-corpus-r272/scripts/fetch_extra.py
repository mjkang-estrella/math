from pathlib import Path
import resource,os,json,hashlib,datetime,concurrent.futures,urllib.request,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);p=Path(__file__).resolve().parents[1]/'sources'
jobs={'fischer-trapezoids.pdf':'https://arxiv.org/pdf/0907.0401','fischer-linear.pdf':'https://arxiv.org/pdf/1008.0527','arnold-citing.pdf':'https://arxiv.org/pdf/0906.0895','miller-author.pdf':'https://www.armiller.org/ReflectionArrangements.pdf','quasirandom.pdf':'https://opikhurko.warwick.ac.uk/E/KralPikhurko13gafa.pdf','pool-projects.yml':'https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/master/lean_projects.yml','pool-page.html':'https://leanprover-community.github.io/lean-pool/','openai-head.html':'https://github.com/openai/math/commits/main/'}
def fetch(job):
 name,url=job;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as h:b=h.read(18000000);r.update(status=h.status,final_url=h.url,sha256=hashlib.sha256(b).hexdigest());(p/name).write_bytes(b)
  if b[:4]==b'%PDF':r['pdftotext_exit']=subprocess.run(['pdftotext','-layout',str(p/name),str((p/name).with_suffix('.txt'))],timeout=12,capture_output=True).returncode
 except Exception as e:r['error']=str(e)
 (p/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 for r in ex.map(fetch,jobs.items()):print(json.dumps(r),flush=True)
