import concurrent.futures, hashlib, json, subprocess, urllib.request
from pathlib import Path
BASE=Path(__file__).resolve().parent
spec=[
('mirek-trojan-v1.pdf','https://arxiv.org/pdf/1405.5566v1'),
('lrr-hal.pdf','https://hal.science/hal-00017086/document'),
('decoupling-v2.pdf','https://arxiv.org/pdf/math/9406214v2'),
('kwapien1987.pdf','https://projecteuclid.org/journals/annals-of-probability/volume-15/issue-3/Decoupling-Inequalities-for-Polynomial-Chaos/10.1214/aop/1176992081.pdf'),
('assani2005.pdf','https://www.impan.pl/shop/en/publication/transaction/download/product/87352'),
('xiao-v2.pdf','https://arxiv.org/pdf/2206.02197v2'),
('kmppw-v4.html','https://arxiv.org/html/2411.09478v4'),
('austin2024.pdf','https://wrap.warwick.ac.uk/id/eprint/189124/1/WRAP-non-convergence-some-non-commuting-double-ergodic-averages-2024.pdf'),
('delarue-home.html','https://delarue.perso.math.cnrs.fr/'),
]
orig=BASE.parent/'i05_crossfield/source-contracts.json'
for x in json.loads(orig.read_text()):
 if any(w in x['path'] for w in ['Rokhlins','Pointwise-Multiple','Triple-ergodic','fourfold']):
  spec.append((x['path'].replace('/','__'),x['url']))
def one(item):
 name,url=item;r={'name':name,'url':url}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'})
  with urllib.request.urlopen(req,timeout=45) as f: data=f.read();r['final_url']=f.url;r['content_type']=f.headers.get('Content-Type')
  (BASE/name).write_bytes(data)
  r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if name.endswith('.pdf'):
   r['valid_pdf']=data.startswith(b'%PDF')
   if r['valid_pdf']:subprocess.run(['pdftotext','-layout',str(BASE/name),str(BASE/name).removesuffix('.pdf')+'.txt'],check=True)
  if name.endswith('.tex'):r['git_blob']=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool: results=list(pool.map(one,spec))
(BASE/'manifest.json').write_text(json.dumps(results,indent=2)+'\n')
for r in results:print(r['name'],r.get('bytes'),r.get('valid_pdf',''),r.get('error',''))
