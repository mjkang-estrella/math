import sys
sys.dont_write_bytecode=True
from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess,concurrent.futures
S=Path(__file__).resolve().parents[2]/'sources/i51_hard_moment_quantitative_stability_novelty'
urls=[('mr-current.html','https://arxiv.org/abs/2511.22636'),('mr.pdf','https://arxiv.org/pdf/2511.22636v3'),('ccm.pdf','https://geometrica.saclay.inria.fr/team/Fred.Chazal/papers/JFOCMboundaryMeasure.pdf')]
def fetch(item):
 name,url=item;p=S/'primary'/name;r={'url':url,'file':str(p.relative_to(S)),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=40) as x:b=x.read();r.update(ok=True,status=x.status,headers=dict(x.headers),final_url=x.url)
 except Exception as e:b=repr(e).encode();r.update(ok=False,error=repr(e))
 p.write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 if b.startswith(b'%PDF'):
  z=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True);p.with_suffix('.txt').write_bytes(z.stdout);r['pdftotext_returncode']=z.returncode
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as e:rows=list(e.map(fetch,urls))
(S/'extra-responses.json').write_text(json.dumps(rows,indent=2)+'\n');print([(r['file'],r['ok']) for r in rows])
