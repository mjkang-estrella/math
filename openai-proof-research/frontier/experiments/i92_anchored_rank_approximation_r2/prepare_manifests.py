#!/usr/bin/env python3
"""Preseal evidence preparation only; never part of the read-only verifier."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i92_anchored_rank_approximation_r2'
assert not (S/'seal.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,obj):(S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def read(p):return (ROOT/p).read_bytes()
F='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/build/'
reads=[]
def passage(p,start,end,scope):
 b=read(p);ls=b.decode().splitlines(keepends=True)
 if end is None:end=len(ls)
 assert 1<=start<=end<=len(ls)
 reads.append(dict(path=p,start=start,end=end,scope=scope,sha256=sha(b),passage_sha256=sha(''.join(ls[start-1:end]).encode()),line_convention='str.splitlines(keepends=True)'))
for section in ['introduction','blocks','operators','walks','tests']:
 passage(F+'sections/'+section+'.tex',1,None,'Complete section, exact contracts and all used lower operations; upstream truth stipulated')
passage(F+'sections/reduction.tex',1,82,'Complete prop:coefficients statement/proof and bounded-coordinate interface')
passage(F+'main.tex',1,None,'Main-file inclusion contract; not reliance on abstract')
passage('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside/preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/main.pdf.txt',626,986,'Complete operative PDF sections 4-6 and theorem-label comparison')
passage('frontier/sources/i88_nonlinear_banach_discovery/external/local-reflexivity.txt',262,280,'Exact Theorem 2.4 interface; standard theorem stated there, not proved there')
passage('frontier/sources/i90_anchored_rank_approximation/external/well-conditioned.txt',257,423,'Theorem 5 complete proof, Auerbach discussion, sampling interface boundary; no sampling theorem used')
for p in ['frontier/iterations/i90-anchored-rank-approximation.md','frontier/iterations/i88-nonlinear-banach-discovery.md']:
 passage(p,1,None,'Complete supplied original report, byte identity checked; analytic review restricted as stated')
for p in ['frontier/experiments/i90_anchored_rank_approximation/verify.py','frontier/experiments/i90_anchored_rank_approximation/diagnostics.py']:
 passage(p,1,None,'Complete code read for evidence replay/diagnostic comparison; not a proof')
save('read-manifest.json',reads)
references={r['path'] for r in reads}
references.update(['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/sources/i88_nonlinear_banach_discovery/search-domain.json','frontier/sources/i88_nonlinear_banach_discovery/seal.json','frontier/sources/i90_anchored_rank_approximation/seal.json','frontier/experiments/i90-parent-verification.json','frontier/iterations/iteration90-anchored-rank-approximation-task.json'])
# Bind each original I90 owned member explicitly as well as checking its exact seal.
old=json.loads(read('frontier/sources/i90_anchored_rank_approximation/seal.json'))
references.update(r['path'] for r in old['files'])
primary=[]
for name,pdf,meta,url,locator,version in [
 ('local-reflexivity','frontier/sources/i88_nonlinear_banach_discovery/external/local-reflexivity.pdf','frontier/sources/i88_nonlinear_banach_discovery/external/local-reflexivity.pdf.response.json','https://users.math.cas.cz/~kania/papers/GoucherKania.pdf','Theorem 2.4, PDF page 7','Retained publisher-style Online First PDF; DOI 10.4064/sm200706-15-1'),
 ('Auerbach','frontier/sources/i90_anchored_rank_approximation/external/well-conditioned.pdf','frontier/sources/i90_anchored_rank_approximation/external/well-conditioned.pdf.response.json','https://www.cs.purdue.edu/homes/pdrineas/documents/publications/Drineas_SICOMP_09.pdf','Section 3.1, pp.2064-2066','Retained SIAM J. Comput. 38(5), 2009 publisher PDF')]:
 text=pdf[:-4]+'.txt';references.update([pdf,text,meta]);primary.append(dict(name=name,pdf=pdf,text=text,response=meta,url=url,locator=locator,version=version,pdf_sha256=sha(read(pdf)),text_sha256=sha(read(text)),new_download=False))
sel=json.loads((S/'selected-inventory.json').read_bytes())
references.update(r['original_local'] for r in sel);references.update(r['local'] for r in sel)
save('primary-evidence.json',primary)
save('immutable-references.json',[dict(path=p,sha256=sha(read(p)),bytes=len(read(p))) for p in sorted(references)])
corpus='frontier/sources/i14_spectral_width_novelty_r3/corpus'
result=subprocess.run(['rg','--files','--no-ignore',corpus],cwd=ROOT,capture_output=True,check=True)
(S/'i14-rg-inventory.txt').write_text('\n'.join(sorted(result.stdout.decode().splitlines()))+'\n')
print(json.dumps(dict(immutable_references=len(references),read_records=len(reads),selected_originals=len(sel),primary_interfaces=len(primary))))
