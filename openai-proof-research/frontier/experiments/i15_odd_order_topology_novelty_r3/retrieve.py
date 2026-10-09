from pathlib import Path
import json,hashlib,datetime,urllib.request,concurrent.futures,subprocess
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i15_odd_order_topology_novelty_r3';L=S/'literature';L.mkdir(exist_ok=True)
old=json.loads((ROOT/'frontier/sources/i15_odd_order_topology_resumed/reading-index.json').read_text())['records']
jobs=[{'name':x['name'],'url':x['url'],'kind':'pdf','prior_sha256':x['pdf_sha256']} for x in old]
for ar in ['0901.0442','2501.12512','2304.10399','2301.06112','2411.19400','2409.02220','2608.30620','2605.27537','2510.21550']:
 jobs.append({'name':'metadata-'+ar,'url':'https://arxiv.org/abs/'+ar,'kind':'html'})
jobs += [{'name':'kremer-2026-current','url':'https://arxiv.org/pdf/2608.30620','kind':'pdf'},{'name':'kremer-borel-current','url':'https://arxiv.org/pdf/2510.21550','kind':'pdf'},{'name':'block-weinberger-center','url':'https://math.uchicago.edu/~shmuel/conner-raymond.pdf','kind':'pdf'}]
def get(job):
 r=dict(job);r['retrieved_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  req=urllib.request.Request(job['url'],headers={'User-Agent':'Mozilla/5.0 (primary-literature-research)'})
  with urllib.request.urlopen(req,timeout=35) as f:b=f.read();r['final_url']=f.url;r['status_code']=f.status;r['content_type']=f.headers.get('Content-Type')
  if job['kind']=='pdf':assert b.startswith(b'%PDF'), 'Not a PDF'
  p=L/(job['name']+'.'+job['kind']);p.write_bytes(b);r.update(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),status='ok')
  if 'prior_sha256' in job:r['equals_prior']=r['sha256']==job['prior_sha256']
  if job['kind']=='pdf':
   q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True,capture_output=True);r['text_path']=str(q.relative_to(ROOT));r['text_sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
 except Exception as e:r.update(status='error',error=repr(e))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
 out=list(pool.map(get,jobs))
(S/'retrieval-manifest.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out:print(r['name'],r['status'],r.get('equals_prior'),r.get('error',''))
