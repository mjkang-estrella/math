"""One-time I55 record assembly. Does not alter any author or shared artifact."""
from pathlib import Path
import json,hashlib,subprocess,sys,os,platform,datetime,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i55_sharp_entropy_stability_r2';A=R/'frontier/sources/i53_sharp_entropy_stability_discovery'
if (S/'passages.json').exists():raise SystemExit('Refusing to overwrite I55 records')
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,o):(S/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
passages=[]
def passage(p,lo,hi,why):
 p=Path(p);lines=p.read_text().splitlines(keepends=True);data=''.join(lines[lo-1:hi]).encode()
 assert 1<=lo<=hi<=len(lines)
 passages.append({'path':str(p.relative_to(R)),'first_line':lo,'last_line':hi,'sha256':sha(data),'role':why})
for p in sorted((A/'pinned').rglob('*.tex')):
 passage(p,1,len(p.read_text().splitlines()),'Actual source proof read; pinned statements and operations are premises, not re-audited upstream claims.')
p=R/'frontier/iterations/i53-sharp-entropy-stability-discovery.md'
for lo,hi,why in [(1,70,'Original scope and inherited inputs'),(71,153,'Slack, mollification, jets and symmetrization'),(154,228,'Original Lemma A'),(229,267,'Original spectral partition construction'),(268,317,'Original law reconstruction, approximation, and primary comparisons'),(318,379,'Original diagnostics, open routes, and reproduction history')]:passage(p,lo,hi,why)
L=S/'literature'
for name,lo,hi,why in [('odeco-v1.txt',348,410,'Exact associativity theorem and simple-ideal proof'),('auddy-v2.txt',640,662,'Already-odeco comparison hypothesis'),('auddy-v2.txt',875,930,'Given nearly isometric factorization hypothesis'),('auddy-v2.txt',2199,2255,'Polar decomposition proof operation'),('sroa-v1.txt',373,445,'Known-near-odeco hypothesis and leading-vector proof'),('sroa-v1.txt',669,776,'Prior deflation budget and assumptions'),('sroa-v1.txt',1173,1225,'Deflation proof expansion'),('fk-v2.txt',1,250,'Normalized norm and matrix-count-dependent partition induction')]:passage(L/name,lo,hi,why)
for name,lo,hi,why in [('fms-v1.txt',320,345,'Entropy formulation'),('fms-v1.txt',588,730,'Auxiliary dimensions and cone proof'),('mnr-author.txt',70,95,'Published scalar sharp theorem'),('mnr-author.txt',249,275,'Rearrangement mechanism'),('mnr-author.txt',426,520,'Degrees of freedom and localization'),('kipp-pdf.txt',190,210,'Local maximizer decomposability bound'),('kipp-pdf.txt',1260,1308,'Moment kernel and second variation proof'),('rademacher-pdf.txt',85,125,'Simplicial local/global extremum statements')]:passage(A/'literature'/name,lo,hi,why)
save('passages.json',passages)
obs=[
('O01','Small L2 error does not control classical derivatives.','Distributional integration by parts against the bump uses one derivative for K and two for DK; uniformly bounded derivatives of q(L) pay the mollification bias.','PASS','1'),
('O02','Gaussian density conversion could lose an extra h power.','On the fixed origin ball the density inverse square root is at most (2pi)^(m/4) exp(R^2/4); no extra h power.','PASS','1'),
('O03','Jet expansion may have repeated-index factors or reversed commutators.','Direct differentiation gives b(XrXt+XtXr); substituting Xt es=Xs et+S_ts gives the original signs.','PASS','1'),
('O04','Symmetrization might destroy normalization or commutation.','Norm estimates (2K+epsilon)epsilon and 4Kepsilon+2epsilon^2 control the two residuals.','PASS','1'),
('O05','Stationarity may be mistaken for a global maximizing direction.','The original explicitly takes a global maximum, obtains the polarization lower bound and constrained Hessian H<=c/2; stationary-only negative control fails.','PASS','2'),
('O06','Associativity identity or bootstrap lower bound c>=1/2 may fail.','Full symmetry and Tv v=cv give the identity; the explicit threshold leaves c^2>1/4.','PASS','2'),
('O07','Restriction might create linear residual growth.','Exact blocks give 2H^2 and h_a h_b^T-h_b h_a^T; both have quadratic norm budgets.','PASS','2'),
('O08','Coefficient-index rotation or recursive error aggregation may omit factors.','All-index orthogonal invariance and disjoint discarded supports yield (96m^2+112m)eta^2<=208m^2eta^2.','PASS','2'),
('O09','Threshold may not close recursively, including eta=0 and m=1.','Total increase is at most 256m^2eta^2<=eta; zero residual and scalar restriction are exact.','PASS','2'),
('O10','B induction may omit block count, contraction or z=0.','Compression preserves contraction; sqrt(d) combines blocks; explicit constant recursion and exact simultaneous diagonalization cover all endpoints.','PASS','3'),
('O11','P inverse control could depend on approximating Hessians or invalid matrix squaring.','Expected spectral-measure Jensen, first-chaos projection, and squaring a single symmetric positive matrix give P>=q(0)I.','PASS','4'),
('O12','Covariance cross moment may have wrong transpose or sign.','For symmetric P, E<F,H>=tr(PM)=tr(PM^T), and ||M||op<=1 gives ||P-I||F<=r.','PASS','4'),
('O13','Nonsmooth densities and moving support might require added assumptions.','Weighted source convergence gives W2 convergence; positive covariance permits continuous whitening; distance to a fixed orbit is 1-Lipschitz.','PASS','4'),
('O14','KL failure may miss reflected or rotated references.','Full support assigns positive mass outside every rotated affine orthant.','PASS','5'),
('O15','Cone transfer or spike arrays could be overclaimed as full theorems.','Only cone-law stability and a matrix-weight obstruction are passed; U and S remain open and spikes are not realized-law counterexamples.','PASS scoped','5'),
('O16','Numerical fixed-orientation values are called upper bounds.','Exact orientation costs bound the orbit distance. Unvalidated Simpson output only approximates those costs; two-resolution agreement certifies no quadrature sign or tail bound. Smallest qualification is recorded in the review only. Neither theorem uses these numbers.','REPORTING QUALIFICATION; no theorem repair','5'),
('O17','A prior tensor theorem could be silently used with weaker hypotheses.','Current primary passages require exact associativity, already-odeco proximity, or a given near-isometric factorization. A and B here are proved directly. No worldwide novelty conclusion.','PASS input audit','6'),
('O18','Re-sealing could erase old verifier failures or conflate ledger drift.','Both old seals/failure records are frozen and hashed. Sorted line multisets and only four mutable-ledger exceptions are used.','PASS evidence scope','Frozen scope')]
save('objections.json',[dict(zip(['id','objection','response','verdict','review_section'],o)) for o in obs])
r=subprocess.run([sys.executable,str(R/'frontier/experiments/i53_sharp_entropy_stability_discovery/verify.py')],cwd=R,capture_output=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
(S/'author-verifier-replay.json').write_bytes(r.stdout)
save('author-replay-process.json',{'returncode':r.returncode,'stderr':r.stderr.decode(),'scope':'Integrity replay only, not the independent analytic verdict'})
assert r.returncode==0, r.stdout.decode()+r.stderr.decode()
versions={}
for p in sorted(L.glob('*-abs.html')):
 text=p.read_text(); versions[p.name]=re.findall(r'\[v\d+\]',text)
save('versions.json',versions)
save('environment.json',{'python':sys.version,'platform':platform.platform(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'network_replay_required':False,'finite_tests':'standard library only; exact fractions plus explicitly uncertified quadrature'})
print(json.dumps({'passages':len(passages),'objections':len(obs),'author_replay':json.loads(r.stdout)},indent=2))
