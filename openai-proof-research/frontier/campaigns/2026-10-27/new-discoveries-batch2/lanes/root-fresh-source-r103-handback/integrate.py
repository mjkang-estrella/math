from pathlib import Path
from fractions import Fraction as F
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent; B=root.parents[1]; lanes=root.parent; repo=B.parents[4]; lane=lanes/'sol-fresh-source-discovery-r103'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(lane/name.lstrip('*'))==h;count+=1
mass=[F(81,100),F(18,100),F(1,100)]; roots=[1,5,7]
normalizer=sum(p/r for p,r in zip(mass,roots)); post=[p/r/normalizer for p,r in zip(mass,roots)]
assert post==[F(2835,2966),F(63,1483),F(5,2966)]
precision=[F(1,r*r) for r in roots];mu=sum(p*x for p,x in zip(post,precision));var=sum(p*(x-mu)**2 for p,x in zip(post,precision));k3=sum(p*(x-mu)**3 for p,x in zip(post,precision))
curvature=3*(F(5,2)*k3+2*mu*var)
assert curvature==F(-5500011742996608,171302489627215625)<0
# Independent formal quotient expansion: posterior mean from exponential tilt.
den=[F(1),-mu/2,sum(p*x*x for p,x in zip(post,precision))/8]
num=[mu,-sum(p*x*x for p,x in zip(post,precision))/2,sum(p*x**3 for p,x in zip(post,precision))/8]
m0=num[0];m1=num[1]-den[1]*m0;m2=num[2]-den[1]*m1-den[2]*m0
assert m1==-var/2 and m2==k3/8
# L(s)=2m+4s*m'-s*m^2; E[Z^4]=3, K''(0)=6*[s²]L.
assert 6*(10*m2-2*m0*m1)==curvature
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED; zero nomination','credit':0,'counts':[8,38],'target':'Eskenazis-Gavalakis Question3: characterize all unit-vector Fisher-information minimizers for arbitrary iid centered Gaussian scale mixtures','root_read':'Full SUMMARY/discovery and completed thread. Re-derived score variational identity, iid swap formula, and equal-point vanishing first density variation.','root_exact_check':{'posterior_weights':list(map(str,post)),'K_second_derivative_at_zero':str(curvature),'independent_method':'Rational exponential-tilt quotient series agrees with cumulant calculation'},'critical_limit':'Negative curvature is near variance0 outside the actual [1,49] variance support. It disproves only the unrestricted K-convexity sufficient lemma, not the source question.','gap':'Universal paired expectation sign at attainable variances, full equality/minimizer classification, and arbitrary-law/infinite-Fisher treatment remain unproved. Even refuting equal weights alone would not answer the full classification.','holds':['Bounded semantic current-registry coverage','No complete prior-art/eligibility clearance'],'failure_notes':'Guarded audit MemoryError preserved, streaming rerun passed without raised caps; exact-id regex correction preserved and full audit rerun.','manifest_entries_verified':count,'summary_sha256':sha(lane/'SUMMARY.md'),'scope':'No PROOF.md, Lean, manuscript or acceptance investment.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('fresh analytic/probabilistic discovery r103.','fresh analytic/geometric discovery r106.')
t=t.replace('Active Sol high/default:','r103 Fisher-mixture minimizer classification remains unresolved. Root independently verified the exact negative K-curvature coefficient; it occurs outside this models attainable variance range and is only a route obstruction. See root-fresh-source-r103-handback/ADOPTION.json.\nActive Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve unresolved Fisher-mixture minimization and scoped curvature obstruction','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
