import sys,json,time,hashlib,resource,urllib.request,urllib.error,subprocess,concurrent.futures
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
items=json.loads((p/sys.argv[1]).read_text())
def get(it):
 name,url=it; t=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());r={'name':name,'url':url,'utc':t}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=18) as f:
   data=f.read(20000000);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(s/name).write_bytes(data)
   if data.startswith(b'%PDF'):
    c=subprocess.run(['pdftotext','-layout',str(s/name),str(s/(name+'.txt'))],capture_output=True,timeout=15);r['pdftotext_returncode']=c.returncode
 except Exception as e:r['error']=repr(e)
 (s/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
 for r in e.map(get,items):print(json.dumps(r),flush=True)
