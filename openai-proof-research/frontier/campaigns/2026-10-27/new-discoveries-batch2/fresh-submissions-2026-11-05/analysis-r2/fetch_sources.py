import urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
out=Path(__file__).parent; (out/'sources').mkdir(exist_ok=True)
items=[(345409,'2002.01884'),(326635,'1311.0028'),(332377,'1602.00436'),(356599,'2210.13922')]
def fetch(item):
 i,a=item;url='https://arxiv.org/pdf/'+a
 r={'id':i,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=45) as f: data=f.read();r['status']=f.status;r['final_url']=f.url
  p=out/'sources'/f'{i}.pdf';p.write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 return r
rows=list(ThreadPoolExecutor(max_workers=4).map(fetch,items));(out/'source-receipts.json').write_text(json.dumps(rows,indent=2));print(rows)
