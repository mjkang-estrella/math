from pathlib import Path
from fractions import Fraction as F
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];lanes=root.parent;repo=B.parents[4];lane=lanes/'sol-fresh-source-discovery-r106'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(lane/name.lstrip('*'))==h;count+=1
# Exact polynomial coefficients for the 3x3 equicorrelation determinant.
# det=1-3r²+2r³, r=-s/2; (1-s)(1+s/2)².
det=[F(1),F(0),F(-3,4),F(-1,4)]
rhs=[F(1),F(1),F(1,4),F(0)]
sq=[F(1),F(1),F(1,4)]
rhs=[(sq[k] if k<3 else 0)-(sq[k-1] if k>0 else 0) for k in range(4)]
assert det==rhs
# Coefficients in q³, q²c, qc² of integrated second-density variation.
coefs=[F(3,4)-F(3,2)+F(3,4),-F(3,2)+F(3,2),F(3,4)]
assert coefs==[0,0,F(3,4)]
# Planar Jensen inequality at rational widths, with duplicate lines permitted.
cases=0
for gaps in ([F(0),F(1,3),F(2,3)],[F(1,6),F(1,3),F(1,2)],[F(1,4)]*4):
    for a in (F(0),F(1,20),F(1,6),F(1,4),F(1,2)):
        assert sum(max(F(0),d-2*a) for d in gaps)>=max(F(0),1-2*len(gaps)*a);cases+=1
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED; one linked family, no nomination','credit':0,'counts':[8,38],'source':'Kunisky2605.02023v1 Conjectures3.1/4.1 full all-correlation absolute Gaussian-minimum tail comparison and all-dimensional equal-zone union comparison','root_read':'Full SUMMARY/discovery and completed thread; re-derived radial implication, planar-gap Jensen, density second variation and small-threshold coefficient contrast.','root_exact_checks':{'equicorrelation_determinant_coefficients':list(map(str,det)),'second_variation_polynomial_coefficients':list(map(str,coefs)),'planar_diagnostic_cases':cases},'route_obstruction':'For feasible Sigma_s with offdiagonal -s/2, Fprime(0)=0 and Fsecond(0)=3c²q/4>0; cyclic endpoint is lower than independent for small positive thresholds since3sqrt(3)<6. Straight monotone/convex interpolation fails, not the source conjecture.','gap':'Global all-rank surface-measure comparison; planar slice widths change under projection. Covering existence and p=2 moment identities do not supply the required stochastic order.','holds':['Both current HEAD requests403: last-known hashes not current certification','Local-stability successor full body403','Inherited aggregate semantic coverage incomplete'],'manifest_entries_verified':count,'summary_sha256':sha(lane/'SUMMARY.md'),'scope':'No PROOF.md, Lean, paper or acceptance. Known rank2 case and helpers uncredited.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('fresh analytic/geometric discovery r106.','fresh analytic/geometric discovery r109.')
t=t.replace('Active Sol high/default:','r106 Kunisky Gaussian-minimum/volumetric-zone conjectures remain unresolved. Root checked covariance second variation and determinant; interpolation obstruction is not a source counterexample. Both live registry HEAD403 and successor-body holds preserved. See root-fresh-source-r106-handback/ADOPTION.json.\nActive Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record unresolved Gaussian minimum comparison and interpolation obstruction','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
