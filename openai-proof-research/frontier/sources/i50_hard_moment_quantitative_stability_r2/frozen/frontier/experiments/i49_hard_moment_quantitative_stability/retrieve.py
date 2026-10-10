#!/usr/bin/env python3
"""One-time primary response capture. Writes only I49 source storage."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import urllib.request,urllib.error,json,hashlib,subprocess,datetime,concurrent.futures
S=Path(__file__).resolve().parents[2]/'sources/i49_hard_moment_quantitative_stability'
DEST=S/'primary';DEST.mkdir(exist_ok=True)
items={
 'centered-v2.pdf':'https://arxiv.org/pdf/2610.10152v2',
 'centered-current.html':'https://arxiv.org/abs/2610.10152',
 'bonnet.pdf':'https://arxiv.org/pdf/2604.09914v1',
 'bonnet-current.html':'https://arxiv.org/abs/2604.09914',
 'klartag.pdf':'https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf',
 'berman.pdf':'https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf',
 'cule.pdf':'https://arxiv.org/pdf/0908.4400',
 'figalli.pdf':'https://people.math.ethz.ch/~afigalli/papers-pdf/Nonlinear-Bounds-in-Holder-Spaces-for-the-Monge-Ampere-Equation.pdf',
 'hug-schneider.pdf':'https://home.mathematik.uni-freiburg.de/rschnei/ArchivHugSchneider.pdf',
 'bh.pdf':'https://users.renyi.hu/~carlos/cone-volume-stability.pdf',
 'bd.pdf':'https://arxiv.org/pdf/2101.02549v6',
 'lu.pdf':'https://arxiv.org/pdf/2608.20730v3',
 'xi.pdf':'https://arxiv.org/pdf/2307.04266v4',
 'vanhandel.pdf':'https://web.math.princeton.edu/~rvan/logzon221121.pdf',
 'minkowski2026.pdf':'https://arxiv.org/pdf/2603.17726',
 'minkowski2026-current.html':'https://arxiv.org/abs/2603.17726',
 'fmp.pdf':'https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf',
 'tensor-fresh.tex':'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/tensor.tex',
 'density-fresh.tex':'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/density.tex',
}
def get(item):
 name,url=item;p=DEST/name;rec={'url':url,'file':'primary/'+name,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research/1.0'}),timeout=45) as f:
   b=f.read();rec.update(status=f.status,final_url=f.url,headers=dict(f.headers));rec['ok']=True
 except urllib.error.HTTPError as exc:
  b=exc.read();rec.update(status=exc.code,ok=False,error=str(exc))
 except Exception as exc:
  b=str(exc).encode();rec.update(status=None,ok=False,error=str(exc))
 p.write_bytes(b);rec.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if b.startswith(b'%PDF'):
  run=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True);rec['pdftotext_returncode']=run.returncode
  if run.returncode:rec['pdftotext_error']=run.stderr.decode(errors='replace')
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: records=list(pool.map(get,items.items()))
(S/'responses.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([{k:r.get(k) for k in ['file','status','ok','bytes']} for r in records],indent=2))
