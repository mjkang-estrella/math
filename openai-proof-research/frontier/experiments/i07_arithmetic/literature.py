import json,hashlib,urllib.request,subprocess,datetime
from pathlib import Path
root=Path(__file__).resolve().parents[3]; out=root/'frontier/sources/i07_arithmetic/literature';out.mkdir(parents=True,exist_ok=True)
sources=[('granville-shao-v1.pdf','https://arxiv.org/pdf/1706.05710v1'),('selberg-delange-v8.pdf','https://arxiv.org/pdf/2010.12929v8'),('selberg-delange-history.html','https://arxiv.org/abs/2010.12929'),('reuss-v1.pdf','https://arxiv.org/pdf/1307.2802v1'),('helfgott-v1.pdf','https://arxiv.org/pdf/1112.3820v1'),('barban-kubilius-shifted.pdf','https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2092-22.pdf'),('pasten.pdf','https://people.math.harvard.edu/~hpasten/preprints/SqfPrimIJNT.pdf'),('hildebrand.pdf','https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/plms/s3-59.2.209')]
rows=[]
for name,url in sources:
 try:
  data=urllib.request.urlopen(url,timeout=35).read(); (out/name).write_bytes(data)
  row={'name':name,'url':url,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'pdf':data.startswith(b'%PDF')}
  if row['pdf']:
   subprocess.run(['pdftotext','-layout',str(out/name),str(out/name.replace('.pdf','.txt'))],check=True)
  elif name.endswith('.pdf'): row['warning']='Not a PDF; not treated as theorem evidence.'
 except Exception as e: row={'name':name,'url':url,'error':str(e)}
 rows.append(row)
(root/'frontier/sources/i07_arithmetic/literature-manifest.json').write_text(json.dumps({'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2)+'\n')
print(json.dumps(rows,indent=2))
