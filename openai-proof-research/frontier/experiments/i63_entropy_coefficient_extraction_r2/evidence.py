"""One-shot metadata for actually read passages and analytic dispositions."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i63_entropy_coefficient_extraction_r2';A=R/'frontier/sources/i61_averaged_entropy_coefficient_rounding'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,x):
 with (S/name).open('x') as f:json.dump(x,f,indent=2,sort_keys=True);f.write('\n')
contracts=[];passages=[]
def read(p,ranges,purpose):
 raw=p.read_bytes();lines=raw.decode().splitlines(keepends=True)
 if ranges=='FULL':ranges=[[1,len(lines)]];scope='FULL'
 else:scope='Only recorded ranges; no full-proof claim beyond these ranges'
 c=dict(path=str(p.relative_to(R)),sha256=sha(raw),ranges=ranges,purpose=purpose,scope=scope);contracts.append(c)
 for a,b in ranges:
  assert 1<=a<=b<=len(lines)
  text=''.join(lines[a-1:b]);passages.append(dict(path=c['path'],start=a,end=b,sha256=sha(text.encode()),text=text))
for p in ['frontier/iterations/i61-averaged-entropy-coefficient-rounding.md','frontier/iterations/i59-dimension-uniform-entropy-stability.md','frontier/iterations/i53-sharp-entropy-stability-discovery.md','frontier/reviews/i55-sharp-entropy-stability-r2.md','frontier/reviews/i56-sharp-entropy-stability-novelty.md']:
 read(S/'inputs'/p,'FULL','Mandatory full original report, not summary-based verdict')
read(R/'frontier/experiments/i61_averaged_entropy_coefficient_rounding/verify.py','FULL','Verify read-only behavior before author replay')
for row in json.loads((S/'pins.json').read_text()):
 p=R/row['frozen'];n=p.name
 if n in ['introduction.tex','transport.tex','matrix.tex','scalar.tex','rigidity.tex','approximation.tex','06-linear-equality.tex','09-consequences.tex','obstruction.tex','10_unital_averaging.tex']:
  read(p,'FULL','Actual premise/application or companion proof; upstream truth stipulated')
 elif n=='certificate.tex':read(p,[[1,160]],'Scalar certificate setup and tail interface; remaining upstream certificates stipulated')
 elif n=='01_introduction.tex':read(p,[[1,75]],'Tracial companion hypotheses and exact theorem scope')
external={
 'kitaev-pdf':([[231,430]],'cb hypotheses, nonpositive spectral rounding, uniform approximate Banach algebra'),
 'bk-pdf':([[60,180],[350,485]],'Pair/family statements and actual weighted averaging modification'),
 'fk-pdf':([[70,230]],'Theorems 2 and 3, block proof and count-dependent iteration'),
 'bdhr-pdf':([[320,415]],'Exact real associative positive-inner-product classification'),
 'bds-journal':([[420,510]],'Published tangent calculation and complex isotropic counterexample scope'),
 'robeva-pdf':([[965,1040]],'Jacobian rank proof of Lemma 3.7'),
 'auddy-pdf':([[640,665],[870,940],[2199,2260]],'Existing odeco/isometric-factor hypotheses and polar proof'),
 'cpv-pdf':([[250,460]],'Exact dagger Frobenius/basis classification and normalization'),
 'poinsot':([[1,40],[155,180],[1187,1228]],'Exact Hilbertian algebra and approximate units, not approximate multiplication')}
for name,(ranges,purpose) in external.items():read(S/'primary'/(name+'.txt'),ranges,purpose)
save('read-contracts.json',contracts);save('passages.json',passages)
comparisons=[]
for name,old in [('bk-pdf','bk2026-pdf'),('kitaev-pdf','kitaev-pdf'),('fk-pdf','fk-pdf'),('cpv-pdf','cpv-pdf'),('bdhr-pdf','bdhr-pdf'),('bds-journal','bds-journal'),('robeva-pdf','robeva-pdf'),('auddy-pdf','auddy-pdf'),('poinsot','hilbert-frobenius')]:
 p=S/'primary'/(name+'.txt');q=A/'literature'/(old+'.txt');assert p.read_bytes()==q.read_bytes()
 comparisons.append(dict(current=str(p.relative_to(R)),earlier=str(q.relative_to(R)),sha256=sha(p.read_bytes()),equal=True))
raw=[]
for row in json.loads((S/'primary/manifest.json').read_text()):
 if row['name'].startswith('pin-'):
  index=int(row['name'][4:]);pin=json.loads((S/'pins.json').read_text())[index];assert (R/row['path']).read_bytes()==(R/pin['frozen']).read_bytes()
  raw.append(dict(response=row['path'],pin=pin['frozen'],git_blob=pin['git_blob']))
save('primary-comparisons.json',comparisons);save('raw-pin-comparisons.json',raw)
verdicts=[('CE61','PASS ORIGINAL WITHOUT REPAIRS','All finite fixed caps, all dimensions, coefficient scope; original explicit modulus and log rate'),('symmetric repair','PASS ORIGINAL WITHOUT REPAIRS','Original already-capped X; constants 26,234,936,2340'),('conditional entropy propagation','PASS ORIGINAL WITHOUT REPAIRS AS CONDITIONAL','Smooth source class and original fixed cap; AR remains a hypothesis'),('I59 inputs as used','PASS ORIGINAL WITHOUT REPAIRS','Separate audits in report paragraph 7, including unused radial theorem'),('channel and deflation partials','PASS ORIGINAL WITHOUT REPAIRS','Generic CP obstruction not linked AR counterexample; adaptive and small-c gaps preserved')]
save('analytic-verdicts.json',[dict(part=a,verdict=b,scope=c) for a,b,c in verdicts])
objections=[
 ('Strict positivity may be only numerical or circular','IFR strictness uses q prime positive first; survival integral gives q second positive and the original compact bounds.'),
 ('Repeated eigenvalues and x-dependent eigenvectors','Continuous divided differences and pointwise tensor rotation; no eigenvectors differentiated.'),
 ('Derivative index not rotated or reflected composition sign','All three indices transform explicitly; the field derivative is evaluated at minus x.'),
 ('Wick crossing claimed positive','It can be negative; row-column norm is enough; explicit negative Clifford example included.'),
 ('Correlated tensor slots require independent Gaussians','Pointwise joint spectral inequality handles the same Gaussian on every slot.'),
 ('Third flattening cap secretly assumed','Fixed marginal traced against operator moment; uncapped-third family included.'),
 ('Random Z incorrectly inserted in fixed V bound','Expand L_j(L_1+L_2)X before expectation; only X is fixed.'),
 ('Ordered curl, projection and reflection factors','Projection commutes with common slot permutation; ordered factor two times reflection factor two.'),
 ('Coefficient commutator expansion requires full symmetry','Only matrix symmetry used; exact S errors paid with B cap.'),
 ('Infimum zero and log quantifiers','Choose cutoff before t, with fixed K and independent m; explicit R threshold and trivial endpoints.'),
 ('Symmetrizing violates cap','Original first-flattening closeness pays discarded mass, then all-slot compression restores cap.'),
 ('Repair changes coefficient-family summation','Full ordered perturbation array bounded by energy caps 1K and 4K.'),
 ('Small normalized error confused with total error','All repair constants homogeneous in total mass and divided by m; no local entrance assumption.'),
 ('Covariance or orientation hidden in entropy propagation','One global U, source P lower bound, and explicit same-space coupling.'),
 ('Cap inherited by nonsmooth approximants','Not claimed or proved; original conditional smooth scope retained.'),
 ('Generic CP counterexample tested only on product bases','Analytic purity bound applies to each vector of every real or complex basis.'),
 ('Normalized super-HS implies cb smallness','Harmonic block plus scalar blocks disproves this implication, not AR.'),
 ('Deflation local identity yields global adaptive control','It does not; small-c and adaptive energy sums remain unpaid.'),
 ('Prior normal derivative closes AR','I56 is local in total distance with dimension-dependent entrance.'),
 ('Quadrature or evidence PASS equals analytic acceptance','Independent derivations give verdict; finite checks and quadrature caveats kept separate.')]
save('objections-and-responses.json',[dict(objection=a,response=b,disposition='Resolved within original scope; no repair') for a,b in objections])
save('work-history.json',dict(preparation=['One initial command used the parent cwd and found no AGENTS.md; no files changed.','Some overlong displayed reads were truncated; substantive original reports/proofs were read in bounded chunks.','Optional NumPy probe reported ModuleNotFoundError; no installation or dependency; final diagnostics use standard library.'],network='21 successful primary requests, no failures; prior failures remain in unchanged prior hashes.',limits=['No external full-theorem certification beyond recorded applicability passages','No proof assistant or human peer review','No priority/count/contribution decision','Finite diagnostics are not universal proof']))
print(json.dumps(dict(contracts=len(contracts),passages=len(passages),objections=len(objections),primary_equalities=len(comparisons),raw_pins=len(raw)),indent=2))
