from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent; B=root.parents[1]; lanes=root.parent; repo=B.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
verified={}; freezes={}
for n in (100,101):
    lane=lanes/f'sol-fresh-source-discovery-r{n}'
    entries=[]
    for line in (lane/'manifest.sha256').read_text().splitlines():
        h,name=line.split(maxsplit=1); name=name.lstrip('*'); assert sha(lane/name)==h; entries.append(name)
    verified[str(n)]=len(entries)
    files={str(p.relative_to(lane)):sha(p) for p in sorted(lane.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
    freezes[str(n)]={'source_lane':str(lane),'files':files}
    (root/f'r{n}-freeze.json').write_text(json.dumps(freezes[str(n)],indent=2)+'\n')
# Independent finite checks of the graph-route obstructions only.
S=[(0,2),(1,0),(2,1)]; dist=lambda a,b:sum(abs(x-y) for x,y in zip(a,b))
assert all(dist(a,b)+dist(b,c)!=dist(a,c) for a,b,c in ((S[i],S[j],S[k]) for i,j,k in ((0,1,2),(0,2,1),(1,0,2))))
assert sorted({p[0] for p in S})==sorted({p[1] for p in S})==[0,1,2]
ds=lambda a,b:0 if a==b else (1 if 0 in (a,b) else 2)
def gp(T):
    return all(ds(a,b)+ds(b,c)!=ds(a,c) and ds(a,c)+ds(c,b)!=ds(a,b) and ds(b,a)+ds(a,c)!=ds(b,c) for a,b,c in combinations(T,3))
def terminal(T):
    return gp(T) and all(any(ds(u,a)+ds(a,b)==ds(u,b) or ds(u,b)+ds(b,a)==ds(u,a) for a,b in combinations(T,2)) for u in set(range(4))-set(T))
sets=[T for k in range(5) for T in combinations(range(4),k) if gp(T)]
assert [T for T in sets if len(T)==max(map(len,sets))]==[(1,2,3)]
assert not terminal((1,2,3)) and terminal((0,1))
# Independent coefficient transform on arbitrary rational sequences, not a test of the imported G-function theorems.
checks=0
for d in range(6):
    a=[F(2*k+1,k+1) for k in range(d+1)]; b=[F(3-k,k+2) for k in range(d+1)]; s=[F((-1)**j*(j*j+2),j+1) for j in range(15)]
    for n in range(15):
        lhs=sum(a[k]*(n-k)*s[n-k]+(k*a[k]+b[k])*s[n-k] for k in range(min(n,d)+1))
        rhs=sum((a[k]*n+b[k])*s[n-k] for k in range(min(n,d)+1)); assert lhs==rhs; checks+=1
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verified_manifest_entries':verified,'r100':{'status':'Full ordinary proof proposed; worker recommends classical exclusion; independent theorem-application and eligibility review pending. Root does not yet adopt full math PASS or exclusion.','root_read':'Full PROOF, SUMMARY and discovery','limited_root_check':f'{checks} exact recurrence-to-ODE coefficient identities; no validation of G-function or Andre theorem applications claimed','review_targets':['Minimal annihilator and Chudnovsky-Katz regular singular/rational exponent applicability','Rank-one algebraicity, rational Puiseux normalization, boundedness after ramification and principal-part removal','Exact source-wide scope and concrete classical subsumption, not shortness alone']},'r101':{'status':'Both lower-general-position claims unresolved; strong-geodetic prism has cited public refutation. No nomination.','root_read':'Full SUMMARY and discovery','limited_root_check':'Actual P3-square projection obstruction and exhaustive K1,3 GP/terminal obstruction pass; not source refutations','missing':['Cardinality-preserving factor compression for synchronized rectangle cover','Witness-preserving terminating replacement for terminal sets'],'holds':['Journal source body','Closest original universal-line body','Bounded semantic registry coverage']},'credit':0,'counts':{'additional':8,'total':38}}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md'; t=p.read_text().replace('fresh graph/finite geometry r101, fresh arithmetic/algebraic r100,','fresh finite/arithmetic discovery r102, independent Matveeva classical-proof review r1,')
line='r100 proposes the full Matveeva4.1 proof via G-functions and Andre; worker self-exclusion is pending independent review, not yet root-adopted. r101 lower general position/terminal existence remain unresolved; exact projection/star obstructions checked. Root manifests, freezes and scoped checks: root-fresh-source-r100-r101-handbacks/ADOPTION.json. No new credit.\n'
t=t.replace('Active Sol high/default:',line+'Active Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lanes/'sol-fresh-source-discovery-r100',lanes/'sol-fresh-source-discovery-r101'):
    paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve Matveeva proof for review and unresolved general-position routes','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
