import json,urllib.request,hashlib,subprocess,concurrent.futures
from pathlib import Path
out=Path('frontier/sources/i05_parity_novelty_r3')
jobs=[('moree-v1.pdf','https://arxiv.org/pdf/math/0307352v1'),('moree-abs.html','https://arxiv.org/abs/math/0307352'),('lt-published.pdf','https://www.utupub.fi/bitstreams/4cedc360-11bd-41ed-bc83-89ab201100ad/download'),('lt-v3.pdf','https://arxiv.org/pdf/2111.08912v3'),('lt-abs.html','https://arxiv.org/abs/2111.08912'),('mathdb-377990.html','https://mathdb.com/p/377990/parity-conjecture-for-the-mobius-function-on-shifted-primes'),('tt-siegel-published.pdf','https://www.utupub.fi/server/api/core/bitstreams/e1f9a4ae-fdcb-41e0-bc35-8ac489c74ca7/content'),('shao-published.pdf','https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf')]
def run(j):
 name,url=j;r={'url':url,'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=35) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  (out/name).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if name.endswith('.pdf'):r['pdftotext_exit']=subprocess.run(['pdftotext','-layout',str(out/name),str(out/Path(name).with_suffix('.txt'))],capture_output=True).returncode
 except Exception as e:r['error']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:res=list(ex.map(run,jobs))
(out/'literature-additional-manifest.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
