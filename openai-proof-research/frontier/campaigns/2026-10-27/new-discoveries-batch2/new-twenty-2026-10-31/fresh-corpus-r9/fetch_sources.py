from pathlib import Path
import requests,json,hashlib,datetime,subprocess,concurrent.futures
p=Path(__file__).resolve().parent
jobs=[('https://api.github.com/repos/openai/math/commits/main','registry-head.json')]+[('https://data.palomar-registry.org/api/v1/results?q='+q,'palomar-'+q+'.json') for q in ['Lissajous','handoff','Lefschetz','sequencing']]+[('https://arxiv.org/pdf/'+a,a+'.pdf') for a in ['1709.09011','1808.00634','1501.03420','1502.01506','1501.01088','1502.07450','1501.06872','1502.06009']]+[('https://drna.padovauniversitypress.it/system/files/papers/Bos_2017_SRM.pdf','Bos_2017.pdf')]
def f(j):
 u,n=j
 try:
  r=requests.get(u,timeout=30);(p/'sources'/n).write_bytes(r.content)
  if r.status_code==200 and r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p/'sources'/n),str((p/'sources'/n).with_suffix('.txt'))],check=True)
  return dict(url=u,file=n,status=r.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content))
 except Exception as e:return dict(url=u,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:r=list(ex.map(f,jobs))
(p/'live-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
