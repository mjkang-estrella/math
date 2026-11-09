import urllib.request,json,hashlib,datetime,subprocess
from pathlib import Path
base=Path(__file__).parent
urls={'V': 'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/36FBA513885E8AEE6447948824BC8243/S0308210500018011a.pdf/div-class-title-higher-monotonicity-properties-of-certain-sturm-liouville-functions-v-a-href-fn01-ref-type-fn-span-class-sup-span-a-div.pdf', 'EL00': 'https://iopscience.iop.org/article/10.1088/0305-4470/33/36/305/pdf', 'GG00': 'https://www.tandfonline.com/doi/pdf/10.1080/10652460008819270'}
rows=[]
for label,url in urls.items():
 r={'label':label,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cap':6000000}
 try:
  with urllib.request.urlopen(url,timeout=30) as f: data=f.read(6000001);r['status']=f.status
  if len(data)>6000000: raise ValueError('cap exceeded')
  ext='pdf' if data.startswith(b'%PDF') else 'html'
  p=base/'sources'/f'{label}.{ext}';p.write_bytes(data)
  r.update(path=str(p),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 rows.append(r)
 (base/'classical-source-receipts.json').write_text(json.dumps(rows,indent=2))
 print(label,r.get('status'),r.get('bytes'),r.get('error'))
