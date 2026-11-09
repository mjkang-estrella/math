import requests,json,hashlib,datetime,resource,concurrent.futures,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources'
jobs=[('zigzag-journal','http://www.seams-bull-math.ynu.edu.cn/downloadfile.jsp?filemenu=_200502&filename=p8.pdf'),('deza2010','https://micheldeza.altervista.org/Preprint10problems.pdf'),('pankov-journal','https://link.springer.com/article/10.1007/s00454-017-9954-z'),('pool-projects','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'),('pool-readme','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/README.md')]
def job(j):
 name,url=j;d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  a=requests.get(url,timeout=12);b=a.content;d.update(status=a.status_code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=a.url);f=s/(name+'.body');f.write_bytes(b)
  if a.status_code==200 and b.startswith(b'%PDF'):d['text_rc']=subprocess.run(['pdftotext','-layout',str(f),str(s/(name+'.txt'))],capture_output=True,timeout=12).returncode
 except Exception as e:d['error']=str(e)
 (s/(name+'.receipt.json')).write_text(json.dumps(d,indent=2));return name,d
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for x in pool.map(job,jobs):print(json.dumps(x),flush=True)
