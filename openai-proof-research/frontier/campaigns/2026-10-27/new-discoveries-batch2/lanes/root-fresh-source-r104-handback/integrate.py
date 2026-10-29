from pathlib import Path
from fractions import Fraction as F
from itertools import product
import hashlib,json,datetime,subprocess
root=Path(__file__).resolve().parent;B=root.parents[1];lanes=root.parent;repo=B.parents[4];lane=lanes/'sol-fresh-source-discovery-r104'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for line in (lane/'MANIFEST.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);assert sha(lane/name.lstrip('*'))==h;count+=1
cases=[]
for n in range(2,9):
    for first in ((F(1,2),F(1,2)),(F(2),F(-1))):
        v=list(first)+[F(0)]*(n-2);pts={tuple(F(1) for _ in v)};zero_signs=0
        for eps in product((-1,1),repeat=n):
            dot=sum(a*b for a,b in zip(v,eps));zero_signs+=(dot==0)
            x=tuple(1-e*dot for e in eps);pts.add(x)
            vx=sum(a*b for a,b in zip(v,x))
            assert all(t*t==2*t-vx for t in x)
        assert len(pts)==1+2**(n-1)-zero_signs//2
        assert len(pts)>=1+2**(n-2)
        if first[0]==F(1,2): assert len(pts)==1+2**(n-2)
        cases.append({'n':n,'v_prefix':list(map(str,first)),'distinct_points':len(pts),'zero_sign_pairs':zero_signs//2})
(root/'exact-checks.json').write_text(json.dumps(cases,indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED; zero nomination','credit':0,'counts':[8,38],'target':'Kaygorodov-Martin Gonzalez-Viruel2610.22248v1 Conjecture6: all complex perfect-evolution-algebra distinct idempotent counts2..2^n','root_read':'Full SUMMARY/discovery and completed thread. Independently re-derived full-support normalization, J1=1 rank-one form, sign parametrization, distinct-pair count and zero-sign bound.','ordinary_route':'L=2I-1*v^t with sum(v)=1 is invertible by determinant lemma (det=2^(n-1)); after x=1+y all y_i² agree. Sign-pair parametrization gives N=1+2^(n-1)-Z >=1+2^(n-2), including complex solutions.','root_exact_checks':{'families':len(cases),'dimensions':[2,8],'includes_negative_weights':True,'scope':'Finite rational diagnostics corroborate the all-complex algebraic route argument; not source conjecture verification.'},'critical_limit':'Fails only the full-support rank-one-Jacobian route to two points for n>=3; higher-rank or sparse-support solutions remain possible. Intermediate-count construction also absent.','other_dispositions':'Worker read actual public C3/C4 automorphism endpoints and quandle successor counterexample; retained as exclusions, no independent external Lean replay or universal truth audit claimed.','holds':['Bounded current registry semantics','No full C6 construction/impossibility argument','No novel result eligible for formal investment'],'manifest_entries_verified':count,'summary_sha256':sha(lane/'SUMMARY.md'),'scope':'No PROOF.md, Lean, paper or acceptance.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';t=p.read_text().replace('fresh structural/algebraic discovery r104,','fresh structural/algebraic discovery r107,');t=t.replace('Active Sol high/default:','r104 complex idempotent-count C6 remains unresolved. Root checked the full-support rank-one-Jacobian sign parametrization and count obstruction; it does not exclude higher-rank/sparse-support constructions. See root-fresh-source-r104-handback/ADOPTION.json.\nActive Sol high/default:',1);p.write_text(t)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Record unresolved complex idempotent spectrum and rank-one route obstruction','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(record))
