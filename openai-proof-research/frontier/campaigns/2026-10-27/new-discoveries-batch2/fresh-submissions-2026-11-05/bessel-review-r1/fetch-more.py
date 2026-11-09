import urllib.request,json,hashlib,datetime,subprocess
from pathlib import Path
base=Path(__file__).parent
urls={
'Filonov':'https://dms.umontreal.ca/~iossif/Bessel.pdf',
'I':'https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5949-11511_2006_Article_BF02391809.pdf',
'III':'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00048021',
'IV':'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/E8E663C1EC768AB22D56A8F89962C7FC/S0008414X00037469a.pdf/higher_monotonicity_properties_of_certain_sturmliouville_functions_iv.pdf',
'V-page':'https://www.cambridge.org/core/journals/proceedings-of-the-royal-society-of-edinburgh-section-a-mathematics/article/higher-monotonicity-properties-of-certain-sturmliouville-functions-v/36FBA513885E8AEE6447948824BC8243',
'openai-current':'https://github.com/openai/math',
'omega-current':'https://github.com/the-omega-institute/trureturing/tree/dev',
'omega-site':'https://www.trureturing.org/conjectures'}
rows=[]
for label,url in list(urls.items())[:1]:
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
 (base/'more-source-receipts.json').write_text(json.dumps(rows,indent=2))
 print(label,r.get('status'),r.get('bytes'),r.get('error'))
