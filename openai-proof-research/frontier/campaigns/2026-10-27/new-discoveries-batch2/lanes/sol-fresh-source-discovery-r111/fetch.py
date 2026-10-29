import urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
lane=Path(__file__).parent
sources=[('exercises','https://arxiv.org/pdf/2210.12842'),('phenomena','https://arxiv.org/pdf/2409.03664'),('maxwell1d','https://staff.math.su.se/shapiro/Articles/Maxwell1D.pdf'),('gns','https://www.math.purdue.edu/~gabriea/maxwell.pdf'),('gns-counter','https://arxiv.org/pdf/2609.09637'),('reverse','https://borowiecki.dev/pdf/2510.09206'),('luo','https://arxiv.org/pdf/2609.11418')]
with (lane/'source-receipts.jsonl').open('w') as log:
 for name,url in sources:
  row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};p=lane/'sources'/(name+'.pdf');h=hashlib.sha256();n=0
  try:
   with urllib.request.urlopen(url,timeout=18) as r,p.open('wb') as f:
    row['status']=r.status;row['final_url']=r.url
    while True:
     b=r.read(65536)
     if not b:break
     n+=len(b)
     if n>16000000:raise ValueError('16MB source cap')
     f.write(b);h.update(b)
   row.update(bytes=n,sha256=h.hexdigest());row['pdftotext_exit']=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=20).returncode
  except Exception as e:row['error']=repr(e)
  log.write(json.dumps(row)+'\n');log.flush();print(json.dumps(row),flush=True)
