#!/usr/bin/env python3
"""Preparation only; writes exclusively I46 evidence."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,datetime,concurrent.futures,urllib.request,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i46_quantitative_logarithmic_stability'
if (S/'artifact-seal.json').exists():
 raise SystemExit('I46 evidence is sealed; this preparation script must not refresh it. Use verify.py.')
items=[(f'{name}-current.html',f'https://arxiv.org/abs/{aid}') for name,aid in [('bd','2101.02549'),('lu','2608.20730'),('xi','2307.04266'),('wang','2510.19061'),('heliu','2510.21530'),('centered','2610.10152'),('clm','1606.06586')]]
items += [('clm-fresh.pdf','https://people.clas.ufl.edu/amarsiglietti/files/CLM_Infinitesimal.pdf'),('local-quant-fresh.pdf','https://glivshyts6.math.gatech.edu/Logbm-zon-corrected.pdf'),('xi-fresh.pdf','https://arxiv.org/pdf/2307.04266v4'),('bd-fresh.pdf','https://arxiv.org/pdf/2101.02549v6'),('centered-fresh.pdf','https://arxiv.org/pdf/2610.10152v2')]
for name in ['reduction','tensor','variance']:
 items.append((name+'-fresh.tex','https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/'+name+'.tex'))
(S/'fresh').mkdir(exist_ok=True)
def fetch(it):
 name,url=it; p=S/'fresh'/name; row={'url':url,'file':str(p.relative_to(S)),'retrieved':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'}),timeout=45) as f:
   b=f.read();row.update(status=f.status,final_url=f.url,ok=True)
 except Exception as exc:
  b=str(exc).encode();row.update(ok=False,error=str(exc))
 p.write_bytes(b);row.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if row['ok'] and name.endswith('.pdf'):
  z=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True);row['pdftotext_returncode']=z.returncode
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: rows=list(ex.map(fetch,items))
(S/'responses.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{'file':r['file'],'ok':r['ok'],'bytes':r['bytes']} for r in rows],indent=2))
