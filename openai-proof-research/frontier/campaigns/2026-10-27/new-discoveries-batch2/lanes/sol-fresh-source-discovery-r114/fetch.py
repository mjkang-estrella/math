import urllib.request,json,hashlib,datetime,subprocess
from pathlib import Path
O=Path(__file__).parent
sources=[
('metric-arxiv.html','https://arxiv.org/html/2412.20558v1'),
('metric-primary.pdf','https://combinatorialpress.com/article/um/Volume%20123/on-some-metric-properties-of-supertoken-graphs.pdf'),
('metric-mathdb.html','https://mathdb.com/p/366438/the-metric-dimension-of-the-supertoken-graph-of-the-complete'),
('metric-successor.html','https://arxiv.org/html/2604.06164v1'),
('localgirth.html','https://arxiv.org/html/2603.25113v1'),
('mycielski.pdf','https://pure.strath.ac.uk/ws/portalfiles/portal/264474107/Kitaev-Pyatkin-DMGT-2024-A-note-on-Hameeds-conjecture-on-the-semi-transitivity.pdf')]
with open(O/'fetch-receipts.jsonl','w') as f:
 for name,url in sources:
  record={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=25) as r:
    record['status']=r.status;record['final_url']=r.url
    p=O/'sources'/name;h=hashlib.sha256();size=0
    with open(p,'wb') as out:
     while b:=r.read(65536):out.write(b);h.update(b);size+=len(b)
    record.update(path=str(p.relative_to(O)),sha256=h.hexdigest(),bytes=size)
   if name.endswith('.pdf'):
    z=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True)
    record['pdftotext_exit']=z.returncode
  except Exception as e:record['error']=str(e)
  f.write(json.dumps(record)+'\n');f.flush();print(json.dumps(record),flush=True)
