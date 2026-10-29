from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations,combinations
from datetime import datetime,timezone
import hashlib,json,subprocess
import sympy as sp
root=Path(__file__).resolve().parent; B=root.parents[1]; lanes=root.parent;repo=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
utc=datetime.now(timezone.utc).isoformat()
freeze=json.loads((lanes/'root-mmpp-survival-review-freeze-r1/review-freeze.json').read_text())['files']
for n,h in freeze.items():assert sha(lanes/'sol-fresh-source-discovery-r90'/n)==h,n
review=lanes/'sol-mmpp-historical-prior-review-r2'
hashes=json.loads((review/'evidence-hashes.json').read_text())
for n,h in hashes.items():assert sha(review/n)==h,n
# Independent symbolic/rational checks supporting the hand-derived Cox bridge.
v,t,eps,mu=sp.symbols('v t eps mu',real=True)
assert sp.trigsimp(sp.sin(v+t/2)-sp.sin(v-t/2)-2*sp.sin(t/2)*sp.cos(v))==0
assert sp.simplify((eps/mu*sp.cos(t/2)*eps*sp.sin(t/2)).subs({eps:sp.Rational(1,2),mu:1,t:3*sp.pi/2}))==-sp.Rational(1,8)
h=F(7,10**12);bound=5*h+F(10,3)*F(6,10**6)
err=h/2+F(5,4)*bound
assert 5*h<F(6,10**6)**2 and err<F(1,3888)
save(root/'ADJUDICATION-HOLD.json',dict(utc=utc,decision='HOLD_SUBSTANTIVE_BOUNDARY_AND_HISTORICAL_PRIORITY',credit=0,counts=[8,38],frozen_candidate_files=len(freeze),review_artifacts_verified=len(hashes),review_sha256=sha(review/'review.md'),ordinary_math='PASS maintained. Root read complete new bridge and checked trigonometric integration, sign, and explicit rational coupling margin; no defect identified.',bridge_check={'cox_gap_coefficient': '-1/8','finite_error_bound':str(err),'error_lt_1_over_3888':True},root_reason='The review constructs a new sinusoidal Cox survival crossing and proves a source-specific finite-MMPP coupling. It explicitly does not locate that crossing or finite bridge in a published theorem. Correctness and elementary ingredients do not alone establish routine subsumption. Root has not adopted the recommendation to exclude.',countercase='All ingredients are standard conditioning, a trigonometric sign integral and Poisson-clock approximation, so routine-construction exclusion is a serious boundary objection. New adjudication must compare actual campaign precedents and full bridge, not just proof length or open-source status.',historical='Thesis relevant public text and withdrawn1802.08400v1 are reconciled as invalid positive-order proofs; exact thesis PDF unavailable. Liu–Neuts1991 and2026moment-paper bodies remain unread.',next='New independent sol-mmpp-classical-boundary-review-r3; no Lean or paper investment, no ledger acceptance/exclusion.'))

lane=lanes/'sol-fresh-source-discovery-r93'; nmanifest=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,n=line.split(maxsplit=1);assert sha(lane/n.strip())==h,n;nmanifest+=1
# Different bounded check: enumerate forbidden-pattern avoidance directly,
# instead of building separables by direct/skew closure as the worker did.
S={1:1};U={1:0}
for n in range(2,7):
    U[n]=sum(((i==1)+U[i])*S[n-i] for i in range(1,n));S[n]=2*U[n]
@lru_cache(None)
def e(n,k):
    if abs(k)>=n:return S[n]
    if n==1:return int(k!=0)
    return p(n,k)+m(n,k)
@lru_cache(None)
def p(n,k):
    if abs(k)>=n:return U[n]
    if n==1:return 0
    return sum(((i==1 and k!=0)+m(i,k))*e(n-i,k) for i in range(1,n))
@lru_cache(None)
def m(n,k):
    if abs(k)>=n:return U[n]
    if n==1:return 0
    return sum(((i==1 and k+n-i!=0)+p(i,k+n-i))*e(n-i,k-i) for i in range(1,n))
rows=[]; checks=0
for n in range(1,7):
    good=[]
    for perm in permutations(range(1,n+1)):
        ok=True
        for inds in combinations(range(n),4):
            a=[perm[i] for i in inds]; rank=tuple(sorted(a).index(z)+1 for z in a)
            if rank in ((2,4,1,3),(3,1,4,2)):ok=False;break
        if ok:good.append(perm)
    assert len(good)==S[n]
    for k in range(-n,n+1):
        literal=sum(all(i+1-z!=k for i,z in enumerate(perm)) for perm in good)
        assert literal==e(n,k),(n,k,literal,e(n,k));checks+=1
    rows.append({'n':n,'separables':len(good),'derangements':e(n,0)})
ad=lanes/'root-fresh-source-r93-handback'
save(ad/'ADOPTION.json',dict(utc=utc,decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],verified_manifest_files=nmanifest,root_validation={'method':'Literal avoidance of2413/3142 vs memoized empty-diagonal recurrence','all_offset_checks':checks,'rows':rows},scope='Root read full discovery and summary. Exact finite checks only, no asymptotic theorem or universal concentration claim.',target='Separable derangement proportion tends to zero,2608.27583v1Conjecture15. Recurrence and advanced endpoint machinery are already public.',gap='Unconditional global occupation/hitting or nonlinear concentration estimate; conditional fixed-offset endpoint system does not prove existence of limits or zero mass.',prior_limits='Actual relevant public statement bodies compared by worker; no root replay of registry Lean. Bounded registry coverage remains incomplete.'))
pnext=B/'NEXT.md';text=pnext.read_text();text=text.replace('MMPP historical-prior review r2, fresh finite/arithmetic r93, fresh analytic/geometric r95.','MMPP classical-boundary adjudication r3, fresh finite/arithmetic r96, fresh analytic/geometric r95. r93 separable derangement asymptotics remains unresolved; root verified its manifest and48 literal forbidden-pattern/empty-diagonal checks through n6. See root-fresh-source-r93-handback/ADOPTION.json. MMPP historical review derived a complete new Cox-to-finite-MMPP proof and recommended routine exclusion; root retains HOLD pending distinction between a new elementary proof and published subsumption. See root-mmpp-boundary-hold-r3/ADJUDICATION-HOLD.json.')
pnext.write_text(text)
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
def commit(folders,files,title):
    paths=list(files)
    for folder in folders:paths.extend(p for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='commit-paths.txt' and p.suffix not in ('.pyc','.olean','.ilean'))
    spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(p.relative_to(repo)) for p in sorted(set(paths)))+'\n')
    subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
    subprocess.run(git+['commit','--quiet','-m',title,'--pathspec-from-file='+str(spec)],cwd=repo,check=True)
    subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
commit([root,review],[],'Preserve MMPP classical bridge and substantive boundary hold')
commit([ad,lane],[pnext],'Preserve unresolved separable derangement recurrence and checks')
print(json.dumps({'mmpp_frozen':len(freeze),'review_hashes':len(hashes),'r93_manifest':nmanifest,'r93_checks':checks,'bridge_error':str(err),'status':'PASS','counts':[8,38]}))
