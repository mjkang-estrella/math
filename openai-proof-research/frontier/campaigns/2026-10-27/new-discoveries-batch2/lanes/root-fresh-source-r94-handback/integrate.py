from pathlib import Path
import hashlib,json,subprocess
from datetime import datetime,timezone
import sympy as s
root=Path(__file__).resolve().parent; B=root.parents[1]; lane=root.parent/'sol-fresh-source-discovery-r94';repo=B.parents[4]
manifest=json.loads((lane/'manifest.json').read_text())
for name,rec in manifest.items():
    p=lane/name
    assert hashlib.sha256(p.read_bytes()).hexdigest()==rec['sha256'],name
    assert p.stat().st_size==rec['bytes'],name
x,a,t=s.symbols('x a t'); H4=x**4-6*x*x+3;r=1+a*H4
assert s.expand(r-24*a*x*x-(a*(x*x-15)**2+1-222*a))==0
def gauss(k): return s.factorial2(k-1) if k else 1
mom=[]
for j in range(5):
    v=s.expand((gauss(2*j)+a*(gauss(2*j+4)-6*gauss(2*j+2)+3*gauss(2*j)))/gauss(2*j))
    assert s.expand(v-(1+4*j*(j-1)*a))==0
    mom.append(v)
assert s.expand(sum(s.binomial(4,j)*(-1)**(4-j)*mom[j] for j in range(5)))==0
assert s.expand(mom[2]-mom[1]**2)==8*a
A=t*t+(1-t)**2
assert s.expand(-s.factorial(4)/2*s.diff(A*A,t,2)+192*(3*t*t-3*t+1))==0
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],verified_manifest_files=len(manifest),root_checks='Exact strong-log-concavity square identity, five Gaussian moment ratios, zero fourth centered mixing moment versus variance8a, and quartic second-variation coefficient PASS.',scope='Root read full discovery and summary. These symbolic checks verify reductions and one mixture obstruction only. No root replay of unvalidated quadratures, no full entropy inequality or source resolution.',target='Luo2609.11418v2 Problem10.1, all symmetric log-concave variance-one densities and Gaussian signal fractions0<q<=4/7.',gap='Full nonlinear all-input entropy curvature; even uniform quartic-family integral sign remains unproved. Fixed-mode concave second variation cannot control growing-degree perturbations.',prior='Worker actual-body screening excludes public symmetric counterexamples for q>4/7 and sample-average moment conjecture. No new credit for those.',registry_hold='Omegad2b0ee6e958cf646530d3476088494e349570b46 advances past2130;90commit300filecappedcomparison and55878pathtruncatedtree do not give complete current coverage.',summary_sha256=hashlib.sha256((lane/'SUMMARY.md').read_bytes()).hexdigest())
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';txt=p.read_text();txt=txt.replace('fresh analytic/probability r94. r74','fresh analytic/geometric r95. r94 Luo Gaussian-smoothing Problem10.1 remains unresolved; root verified51 manifest entries and exact Hermite curvature/mixing obstructions. Current-registry truncation HOLD remains. See root-fresh-source-r94-handback/ADOPTION.json. r74');p.write_text(txt)
paths=[p]
for folder in (root,lane):
    paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve unresolved Gaussian smoothing reductions and exact obstructions','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'manifest_files':len(manifest),'root_checks':'PASS','counts':[8,38]}))
