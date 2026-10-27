import requests,json,hashlib
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
p=Path(__file__).resolve().parent
urls={
 'imc2024-official-www':'https://www.imc-math.org.uk/imc2024/imc2024-day1-solutions.pdf',
 'imc2024-official-http':'http://imc-math.org.uk/imc2024/imc2024-day1-solutions.pdf',
 'imc1994-2024-uoa':'https://eclass.uoa.gr/modules/document/file.php/MATH206/IMC%201994%20to%202024%20with%20solutions.pdf',
}
def get(item):
 n,u=item
 try:
  r=requests.get(u,timeout=35,headers={'User-Agent':'Mozilla/5.0'})
  pdf=r.content.startswith(b'%PDF');ext='.pdf' if pdf else '.html'
  (p/(n+ext)).write_bytes(r.content)
  return {'name':n,'url':u,'status':r.status_code,'bytes':len(r.content),'is_pdf':pdf,'type':r.headers.get('content-type'),'sha256':hashlib.sha256(r.content).hexdigest(),'file':n+ext}
 except Exception as e:return {'name':n,'url':u,'error':str(e)}
with ThreadPoolExecutor(max_workers=3) as ex:out=list(ex.map(get,urls.items()))
(p/'fetch-receipts.json').write_text(json.dumps(out,indent=2)+'\n')
for v in out:print(v['name'],v.get('status'),v.get('is_pdf'),v.get('bytes'))
