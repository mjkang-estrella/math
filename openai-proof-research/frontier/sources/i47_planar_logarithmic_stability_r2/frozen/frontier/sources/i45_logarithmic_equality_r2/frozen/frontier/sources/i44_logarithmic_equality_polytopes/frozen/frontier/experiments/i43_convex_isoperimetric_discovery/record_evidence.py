#!/usr/bin/env python3
"""Preparation only: writes exclusively to this task's assigned evidence paths."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,shutil,requests,datetime,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i43_convex_isoperimetric_discovery'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(name,obj):(S/name).write_text(json.dumps(obj,indent=2)+'\n')
# Remove only our unused exploratory entropy snapshot; no dependency claimed.
for p in (S/'pinned/preprints').glob('A-sharp-entropy*'):shutil.rmtree(p)
extra=['frontier/iterations/i02-crossfield.md']
for p in extra:
 t=S/'frozen'/p;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/p,t)
paths=sorted(p for p in (S/'pinned').rglob('*') if p.is_file())
manifest=json.loads((S/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text());lookup={x['path']:x for x in manifest['files']}
selected=[]
for p in paths:
 rel=str(p.relative_to(S/'pinned'));row=dict(lookup[rel]);assert sha(p)==row['sha256'];selected.append(row)
put('selected-manifest.json',{'pin':PIN,'files':selected});put('selected-paths.json',[x['path'] for x in selected])
put('frozen-inputs.json',[{'path':str(p.relative_to(S/'frozen')),'sha256':sha(p)} for p in sorted((S/'frozen').rglob('*')) if p.is_file()])
L='preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/'
T='preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/'
P='preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/'
PM='preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/build/latex/'
contracts=[(L+'introduction.tex',['thm:main','cor:lp'],'Global inequality and positive-p transfer; no equality classification.'),(L+'reduction.tex',['prop:variance','eq:slabs','eq:partition-concavity'],'Soft slab variance, curvature, and ordered hard-boundary/direction limits.'),(L+'moment.tex',['lem:moment'],'Moment map, upper Hessian 4/epsilon and only local lower positivity.'),(L+'identities.tex',['eq:test-pairing','eq:W-gradient','eq:hessian'],'Double divergences and Hessian energy.'),(L+'density.tex',['lem:density'],'L2 density; no parameter-uniform inverse.'),(L+'tensor.tex',['lem:tensor','eq:tensor-squares'],'Actual explicit nonnegative tensor remainder.'),(L+'variance.tex',['eq:first-cs','eq:second-cs','eq:dual-bound'],'Summandwise CS operations and dual contraction.'),(L+'measure.tex',['cor:measure','eq:relative-wulff-inclusion'],'Already pays even log-concave Radon support reduction and scalar B.'),(T+'paper.tex',['intro:main'],'All cubic minimizers and both transitions.'),(T+'sections/preliminaries.tex',['pre:structure','pre:standard','pre:reduction'],'Classical low-genus types and two-volume reduction.'),(T+'sections/nesting.tex',['nest:bottom-calibration','nest:shape-gain','nest:area-bound'],'Corner calibration/nesting and integrated cubic gain at cubic endpoint.'),(P+'main.tex',['prop:product','prop:simplex','cor:exponential-excess'],'Product mechanism and its already explicit large-n iteration.'),(PM+'sections/01_introduction.tex',['thm:main'],'Lower projection-volume inequality, not upper bound.')]
put('source-contracts.json',[{'path':path,'labels':labels,'operation':op,'url':'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path} for path,labels,op in contracts])
# Fresh independent raw responses for key accepted operations.
rows=json.loads((S/'responses.json').read_text())
need=[L+'reduction.tex',L+'tensor.tex',T+'paper.tex',P+'main.tex']
D=S/'fresh';D.mkdir(exist_ok=True)
def fetch(path):
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path;rec={'name':'fresh-'+path.split('/')[1],'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=25);p=D/(path.split('/')[1]+'__'+Path(path).name);p.write_bytes(r.content);rec.update(status=r.status_code,final_url=r.url,file=str(p.relative_to(S)),sha256=sha(p),ok=r.status_code==200)
  rec['matches_pinned']=r.content==(S/'pinned'/path).read_bytes()
 except Exception as e:rec.update(ok=False,error=str(e))
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:new=list(ex.map(fetch,need))
rows+=new;put('responses.json',rows)
# Logged passages reflect reads used, not a claim to have audited whole external books/papers.
reads=[]
for path,labels,op in contracts:
 p=S/'pinned'/path
 if path.startswith(L): ranges=[(1,len(p.read_text().splitlines()))]
 elif 'nesting.tex' in path:ranges=[(1,145),(178,366),(504,573)]
 elif 'preliminaries.tex' in path:ranges=[(1,230)]
 else:ranges=[(1,len(p.read_text().splitlines()))]
 reads.append((str(p.relative_to(S)),ranges,op))
reads += [('literature/lu2026.txt',[(80,173),(370,455),(500,524)],'Current v3 statement and actual equality/fiber/dilation/first-variation mechanisms'),('literature/vanhandel.txt',[(130,192),(714,795),(1020,1060)],'Nonsmooth local equality, mixed-area identity, explicit global approximation limitation'),('literature/bd2025.txt',[(255,301)],'Quantitative reflection-class theorem and corner-cut degeneration'),('literature/putterman.txt',[(35,250),(250,315)],'Local-global theorem, p-limit strictness distinction, first variation and polytope setup'),('literature/afm.txt',[(175,235)],'Actual quadratic local periodic perimeter remainder, including gamma=0'),('literature/reverseprojection.txt',[(15,115)],'Current dimension-nine counterexamples and explicit open dimensions 4--8'),('literature/huivaki.txt',[(1,160)],'Polytope spectrum main scope, facet network, conditional bound below n')]
D=S/'read-passages';D.mkdir(exist_ok=True)
records=[]
for j,(path,ranges,note) in enumerate(reads):
 p=S/path;lines=p.read_text().splitlines();chunks=[]
 for a,b in ranges:
  b=min(b,len(lines));chunks.extend(f'{i}: {lines[i-1]}' for i in range(a,b+1))
 target=D/f'{j:02d}.txt';target.write_text('\n'.join(chunks)+'\n');records.append({'path':path,'sha256':sha(p),'ranges':ranges,'note':note,'extract':str(target.relative_to(S))})
put('read-passages.json',records)
put('preparation-notes.json',{'initial_diagnostic_dependency_failure':'Initial symbolic checker could not import sympy; replaced by a stdlib Fraction/polynomial implementation. No installation or external-path writes performed.','draft_correction':'Before sealing, paired normalized cone-volume norm corrected to 2/(2+delta) and ratio 2delta/(2-delta); exact checks verify both.','unused_snapshot_removed':'Exploratory entropy-family copy removed from this task directory; not used.','scope':'No analytic target accepted. No worldwide-priority certification.'})
print(json.dumps({'selected_files':len(selected),'fresh':[(r['ok'],r.get('matches_pinned')) for r in new],'read_records':len(records)}))
