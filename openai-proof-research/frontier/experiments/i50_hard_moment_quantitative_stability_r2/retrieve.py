#!/usr/bin/env python3
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i50_hard_moment_quantitative_stability_r2';D=S/'primary';D.mkdir(exist_ok=True)
urls={
'centered-current.html':'https://arxiv.org/abs/2610.10152',
'centered-v2.pdf':'https://arxiv.org/pdf/2610.10152v2',
'bonnet-current.html':'https://arxiv.org/abs/2604.09914',
'bonnet.pdf':'https://arxiv.org/pdf/2604.09914v1',
'berman.pdf':'https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf',
'cule.pdf':'https://arxiv.org/pdf/0908.4400',
'figalli.pdf':'https://people.math.ethz.ch/~afigalli/papers-pdf/Nonlinear-Bounds-in-Holder-Spaces-for-the-Monge-Ampere-Equation.pdf',
'klartag.pdf':'https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf',
'hug-schneider.pdf':'https://home.mathematik.uni-freiburg.de/rschnei/ArchivHugSchneider.pdf',
'fmp.pdf':'https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf',
'klr.pdf':'https://arxiv.org/pdf/2507.12099v3',
}
for name in ['tensor','density']:
 urls[name+'-fresh.tex']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/'+name+'.tex'
def fetch(kv):
 name,url=kv;r={'file':'primary/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=45) as res:b=res.read();r.update(status=res.status,headers=dict(res.headers),final_url=res.url)
 except urllib.error.HTTPError as ex:b=ex.read();r.update(status=ex.code,error=str(ex))
 except Exception as ex:b=str(ex).encode();r.update(status=None,error=str(ex))
 (D/name).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),ok=r.get('status')==200)
 prior=R/'frontier/sources/i49_hard_moment_quantitative_stability/primary'/name
 if prior.exists():r['matches_I49_bytes']=b==prior.read_bytes()
 if b.startswith(b'%PDF'):
  p=subprocess.run(['pdftotext','-layout',str(D/name),'-'],capture_output=True);r['pdftotext_returncode']=p.returncode;(D/name).with_suffix('.txt').write_bytes(p.stdout)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: records=list(pool.map(fetch,urls.items()))
(S/'responses.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([{k:r.get(k) for k in ['file','status','bytes','matches_I49_bytes','error']} for r in records],indent=2))
