import urllib.request,hashlib,json,datetime,subprocess,sys
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
out=Path(__file__).parent;(out/'sources').mkdir(exist_ok=True)
items=[tuple(a.split('=',1)) for a in sys.argv[1:]]
def fetch(item):
 i,url=item;r={'id':i,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'research-fetch/1.0'})
  with urllib.request.urlopen(req,timeout=40) as f:data=f.read(15000001);r['status']=f.status;r['final_url']=f.url
  assert len(data)<=15000000
  p=out/'sources'/f'{i}.pdf';p.write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest();r['bytes']=len(data)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 return r
rows=list(ThreadPoolExecutor(max_workers=4).map(fetch,items))
rp=out/'source-receipts.json'; old=json.loads(rp.read_text()) if rp.exists() else []
rp.write_text(json.dumps(old+rows,indent=2));print(json.dumps(rows,indent=0))
