from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from datetime import datetime,timezone
import json,hashlib,subprocess
import sympy as s
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4];lane=root.parent/'sol-fresh-source-discovery-r95'
manifest=json.loads((lane/'manifest.json').read_text())
for rec in manifest:
    p=lane/rec['path'];assert p.stat().st_size==rec['bytes'];assert hashlib.sha256(p.read_bytes()).hexdigest()==rec['sha256'],rec['path']
z,c=s.symbols('z c',positive=True);D=s.sqrt(1+z-z*c*c);u=s.sqrt(1-c*c)
f=z*c+D-1;g=2*s.sqrt(z*(1+z))*c+s.sqrt(z)*u*s.atan(s.sqrt(1+z)*u/c)
at={z:s.Rational(14,11),c:s.Rational(5,6)}
fz=s.diff(f,z).subs(at);fcc=s.diff(f,c,2).subs(at)
H=s.diff(g,c,2).subs(at)-s.diff(g,z).subs(at)*fcc/fz
expected=-s.Rational(266733,590359)*s.sqrt(14)*s.pi+s.Rational(2700,53669)*s.sqrt(7)*s.pi+s.Rational(308016,1341725)*s.sqrt(14)+s.Rational(875664,590359)*s.sqrt(7)
assert s.simplify(H-expected)==0 and fz>0
assert s.simplify(f.subs(at)-(s.Rational(2,33)+5*s.sqrt(2)/6))==0
# A separately chosen 12-term Machin enclosure and 10^9 sqrt grid suffice.
def arctan(q):
    low=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(12)),F(0))
    return low,low+F(1,25*q**25)
l5,h5=arctan(5);l239,h239=arctan(239);pi=(16*l5-4*h239,16*h5-4*l239)
def sqrt_bounds(n):
    d=10**9;k=isqrt(n*d*d);assert k*k<n*d*d<(k+1)**2;return F(k,d),F(k+1,d)
r14=sqrt_bounds(14);r7=sqrt_bounds(7)
low=-F(266733,590359)*r14[1]*pi[1]+F(2700,53669)*r7[0]*pi[0]+F(308016,1341725)*r14[0]+F(875664,590359)*r7[0]
high=-F(266733,590359)*r14[0]*pi[0]+F(2700,53669)*r7[1]*pi[1]+F(308016,1341725)*r14[1]+F(875664,590359)*r7[1]
assert low<=high<-F(1,10)
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],manifest_files_verified=len(manifest),root_checks={'direct_symbolic_constrained_hessian':True,'fixed_area_reference_identity':True,'hessian_rational_interval':[str(low),str(high)],'upper_lt_minus_one_tenth':True},root_scope='Read full discovery and summary. Independently directly differentiated the supplied geometric f,g formulas; different rational interval precision confirms sign. No root validation of global geometric formulas against primary pages, no minimizer classification, no source refutation.',target='Hong2606.01771v4 Question5.5, characterize all compact hyperbolic convex fixed-area mean-curvature minimizers.',obstruction='Equal-cap replacement can worsen mean curvature at fixed area for a nonstationary symmetric drum. This neither refutes source Question5.5 nor axial symmetry: both perturbed bodies remain axial and original drum need not be optimal.',gap='No comparison from every convex body to a justified model family; even optimizing drums alone would not solve full scope.',prior='Worker read public Zhangv2 and Shenv3 proof bodies excluding sharp zero-sum norm and boundary-distance leads. No credit for those.',freshness='Omega a5a8bcdf56019e58c398f6f6d27a3620b896d001 observed19:22; small2commit1filedelta does not independently fill broader inherited coverage holds.',summary_sha256=hashlib.sha256((lane/'SUMMARY.md').read_bytes()).hexdigest())
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';txt=p.read_text();txt=txt.replace('fresh analytic/geometric r95.','fresh analytic/geometric r97. r95 Hong hyperbolic minimizers remain unresolved; root checked exact constrained Hessian and negative sign, only a symmetrization-route obstruction. See root-fresh-source-r95-handback/ADOPTION.json.');p.write_text(txt)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve Hong minimizer gap and exact symmetrization obstruction','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'manifest_files':len(manifest),'exact_checks':'PASS','counts':[8,38]}))
