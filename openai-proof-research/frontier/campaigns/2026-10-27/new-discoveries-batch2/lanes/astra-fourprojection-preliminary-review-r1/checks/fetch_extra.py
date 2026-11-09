from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,hashlib,json,datetime,subprocess
B=Path(__file__).resolve().parents[1];S=B/'sources'
items={
'banica-book.pdf':'https://vixra.org/pdf/2009.0045v1.pdf',
'polar-relative.pdf':'https://www.netlib.org/lapack/lawnspdf/lawn83.pdf',
'polar-absolute.pdf':'https://www2.eecs.berkeley.edu/Pubs/TechRpts/1994/CSD-94-852.pdf',
'frames.pdf':'https://arxiv.org/pdf/math/9812052',
'partial-isometry.pdf':'https://iam.conicet.gov.ar/wp-content/uploads/sites/222/2025/04/506.pdf',
'sudoq.pdf':'https://arxiv.org/pdf/2005.10862',
'modeling.pdf':'https://arxiv.org/pdf/1704.00290',
'orbitals.pdf':'https://arxiv.org/pdf/2302.05902',
'higher-transitive.pdf':'https://arxiv.org/pdf/1712.04067',
}
def get(x):
 n,u=x;d=dict(file=n,url=u,accessed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  r=requests.get(u,timeout=30);(S/n).write_bytes(r.content);d.update(status=r.status_code,final_url=r.url,bytes=len(r.content),sha256=hashlib.sha256(r.content).hexdigest())
  if r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(S/n),str(S/n.replace('.pdf','.txt'))],check=True)
 except Exception as e:d['error']=str(e)
 return d
with ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(get,items.items()))
p=S/'retrievals.json';p.write_text(json.dumps(json.loads(p.read_text())+rows,indent=2))
for r in rows:print(r['file'],r.get('status'),r.get('bytes'),r.get('error',''))
