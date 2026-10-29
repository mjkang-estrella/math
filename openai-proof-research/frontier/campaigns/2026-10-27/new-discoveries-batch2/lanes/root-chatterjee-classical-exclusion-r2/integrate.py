from pathlib import Path
from fractions import Fraction as F
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent; B=root.parents[1]; lanes=root.parent; repo=B.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
review=lanes/'sol-chatterjee-source-prior-review-r2'
checked={}
for label,manifest in [('candidate',lanes/'root-chatterjee-triangle-review-freeze-r1/review-freeze.json'),('preliminary',lanes/'root-chatterjee-preliminary-adoption-r1/review-hashes.json')]:
    d=json.loads(manifest.read_text()); source=Path(d['source_lane'])
    for name,h in d['files'].items():
        assert sha(source/name)==h
        assert sha(review/'inputs'/label/name)==h
    checked[label]=len(d['files'])
d=json.loads((review/'evidence-manifest.json').read_text())
for name,h in d['files'].items(): assert sha(review/name)==h
checked['review_evidence']=len(d['files'])
# Exact specialization of the old dyadic sorting construction for the modulo-two pair.
# U=(I+V)/2; V=(J+T)/m; B=(2J+I+T)/(2m), with I fair.
# A=V, C=U: B<->C bijective, A|B deterministic, B|A two equal atoms.
tests=[]
for j in range(1,12):
    m=2**j
    atom_gap=F(1,2*m)
    e=3*sum(F(1,4)*abs(i-k)*atom_gap for i in (0,1) for k in (0,1))
    assert e==F(3,4*m)
    end=3*sum(F(1,4)*F(abs(i-k),2) for i in (0,1) for k in (0,1))
    assert end==F(3,4) and end/e==m
    # Common independent mixing has the same affine map for directed/avg/max.
    for K in (F(1,3),F(1),F(5),F(20)):
        if m<=2*K: continue
        for a,b in ((end,e),(end/2,e/2)):
            gap=a-K*b; eps=min(F(1,100),gap/(8*(1+2*K)))
            t=(1-eps)**2; c=1-t
            actual=(t*a+c)-K*(t*b+2*c)
            assert actual==t*gap+(1-2*K)*c and actual>0
            assert c>0
    tests.append({'m':m,'dAB':str(e),'dAC':str(end),'all_three_ratio':m})
(root/'exact-checks.json').write_text(json.dumps(tests,indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'EXCLUDE_ROUTINE_CLASSICAL_COROLLARY','credit':0,'counts':[8,38],'ordinary_math':'PASS retained; exact candidate six formulas not claimed previously published','source':'Accepted-manuscript multiplicative question PASS; final published version HOLD unchanged','root_inspection':'Read complete review and actual cached Ruankong Sobolev norm/Theorem2.1/Theorem5.4 proof through its conclusion; Ansari-Wiesel definitions16-21 and Lemma2.5. Re-derived compatible triple, all-K ratios, common checkerboarding and affine independent-mixture identity.','bridge':'Ruankong et al. arXiv1204.0405 Theorem5.4 proof reorders U by a.e. invertible measure-preserving maps b_j so Copula(b_j(U),f(U)) approaches Sobolev norm1 on the same space. For A=2U mod1, B=b_j(U), C=U, BC distances vanish, AC=3/4, CA=0 and AB tends0 while BA=0. Thus all3 triangle ratios diverge. Common trivariate checkerboarding preserves pair compatibility; Ansari-Wiesel2606.07354 Lemma2.5 and |xi_q-xi|<=12d1 give six-value convergence. Independent common mixing gives d_e=(1-e)^2 d+2e-e^2, preserving strict violations and positive distances. Taking sufficiently close checkerboards also keeps every xi>0, hence distances<1.','countercase':'Candidate gives convenient exact nonsingular formulas and was independently invented; preliminary provisional PASS was reasonable without this actual old compatible-triple construction. It is now superseded by positive primary-body evidence, not by shortness or a newly invented alternative alone.','novelty':'No claim that exact endpoint was printed previously; broader historical/registry coverage remains bounded. Concrete classical subsumption suffices for campaign exclusion.','verification':checked,'limited_exact_checks':'11 dyadic modulo-two sorting specializations and rational affine-mixture margin checks; diagnostics separate from cited all-order theorem proof','review_sha256':sha(review/'review.md'),'primary_sha256':{name:sha(review/'live'/name) for name in ('ruankong.pdf','adapted.pdf')},'scope':'Stop Lean/paper/acceptance investment; preserve candidate, preliminary contrary judgment, source HOLD and all failures.'}
(root/'EXCLUSION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md'; t=p.read_text(); t=t.replace('Chatterjee final-source/trivariate-prior review r2.','fresh analytic/probabilistic discovery r103.')
t=t.replace('Independent review confirms ordinary mathematics and full accepted-manuscript multiplicative scope, with provisional substantive PASS. Published-version comparison and targeted compatible-triple/copula prior-art clearance remain HOLD. Root adoption: root-chatterjee-preliminary-adoption-r1/ADOPTION.json.','Chatterjee is now EXCLUDED as a routine classical corollary: actual Ruankong Theorem5.4 proof supplies the compatible triple, with published checkerboard convergence and common mixture preserving full regularity. Root inspected primary passages and re-derived the bridge. Math and accepted-manuscript scope PASS retained; published-version HOLD separate; preliminary provisional PASS preserved historically. See root-chatterjee-classical-exclusion-r2/EXCLUSION.json.')
p.write_text(t)
paths=[p]
for folder in (root,review): paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Exclude Chatterjee triangle result through published compatible-triple bridge','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
