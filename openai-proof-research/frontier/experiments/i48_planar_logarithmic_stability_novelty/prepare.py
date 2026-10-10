#!/usr/bin/env python3
"""One-time evidence preparation; writes only I48 sources/experiments."""
import sys
sys.dont_write_bytecode=True
import json, hashlib, shutil, subprocess, urllib.request, urllib.error, datetime, concurrent.futures
from pathlib import Path
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i48_planar_logarithmic_stability_novelty';E=Path(__file__).resolve().parent
assert not (S/'artifact-seal.json').exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mutable={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
paths=list(mutable)+['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json']
for n,slug in [(43,'convex_isoperimetric_discovery'),(44,'logarithmic_equality_polytopes'),(45,'logarithmic_equality_r2'),(46,'quantitative_logarithmic_stability')]:
 base=f'frontier/sources/i{n}_{slug}'
 paths += [base+'/brief.txt',base+'/artifact-seal.json'] if (R/base/'brief.txt').exists() else [base+'/artifact-seal.json']
paths += ['frontier/iterations/i43-convex-isoperimetric-discovery.md','frontier/iterations/i44-logarithmic-equality-polytopes.md','frontier/reviews/i45-logarithmic-equality-r2.md','frontier/iterations/i46-quantitative-logarithmic-stability.md','frontier/iterations/iteration46-i45-dependency-update.json','frontier/experiments/i46-parent-verification.json','frontier/experiments/i45-parent-verification.json','frontier/sources/i46_quantitative_logarithmic_stability/dependency-update.txt','frontier/sources/i46_quantitative_logarithmic_stability/source-contracts.json','frontier/sources/i46_quantitative_logarithmic_stability/inherited-selected-manifest.json']
rows=[]
for rel in sorted(paths):
 p=R/rel;q=S/'frozen'/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);rows.append(dict(path=rel,sha256=sha(p),mutable=rel in mutable))
(S/'frozen-inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
old=R/'frontier/sources/i46_quantitative_logarithmic_stability'
shutil.copytree(old/'pinned',S/'pinned',dirs_exist_ok=True)
items=[('blyz.pdf','https://math.nyu.edu/~yangd/papers/LBMI.pdf'),('vanhandel.pdf','https://web.math.princeton.edu/~rvan/logzon221121.pdf'),('klartag.pdf','https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf'),('cone-volume.pdf','https://users.renyi.hu/~carlos/cone-volume-stability.pdf')]
for name,aid in [('xi2026','2609.08495v1'),('xi','2307.04266v4'),('bd','2101.02549v6'),('lu','2608.20730v3'),('clm','1606.06586'),('cl','1710.10708'),('wang','2510.19061v2'),('heliu','2510.21530v1'),('lsx','2610.10152v2'),('cheeger','0910.3118'),('nearconstant','2407.04179')]:
 if name=='nearconstant':continue
 items.extend([(name+'.pdf','https://arxiv.org/pdf/'+aid),(name+'-current.html','https://arxiv.org/abs/'+aid.split('v')[0])])
items.append(('pinned-reduction.tex','https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/reduction.tex'))
def fetch(it):
 name,url=it;p=S/'primary'/name;row=dict(file=str(p.relative_to(S)),url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=40) as f:b=f.read();row.update(ok=True,status=f.status,final_url=f.url)
 except urllib.error.HTTPError as exc:b=exc.read();row.update(ok=False,status=exc.code,error=str(exc))
 except Exception as exc:b=str(exc).encode();row.update(ok=False,error=str(exc))
 p.write_bytes(b);row.update(sha256=sha(p),bytes=len(b))
 if row['ok'] and name.endswith('.pdf'):
  z=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True);row['pdftotext_returncode']=z.returncode
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:rows=list(ex.map(fetch,items))
(S/'responses.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([dict(file=x['file'],ok=x['ok'],bytes=x['bytes']) for x in rows],indent=2))
