from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
from math import comb
import json,hashlib,subprocess
import sympy as s
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4];lane=root.parent/'sol-fresh-source-discovery-r98'
count=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,n=line.split(maxsplit=1);assert hashlib.sha256((lane/n.strip()).read_bytes()).hexdigest()==h,n;count+=1
x,t=s.symbols('x t')
def rising(n):return s.Poly(s.prod(x+j for j in range(n)),x)
def b(n,j):return rising(n-j)*rising(j)
row=b(7,0)+21*b(7,2)
assert row==s.Poly(2*x*(x+1)*(x+2)*(x+3)*(x+4)*(11*x*x+16*x+15),x)
assert 16**2-4*11*15==-404
def defect(p,i):return p.nth(i)**2-p.nth(i-1)*p.nth(i+1)
def cross(p,q,i):return 2*p.nth(i)*q.nth(i)-p.nth(i-1)*q.nth(i+1)-q.nth(i-1)*p.nth(i+1)
assert cross(b(17,0),b(17,7),7)==-101773398996093086080
p,q=b(35,0),b(35,16);c=cross(p,q,17);dq=defect(q,17)
w=-F(int(c),2*int(dq));negative=F(int(defect(p,17)))-F(int(c*c),4*int(dq))
assert w>0 and negative<0
Hs=[sum((b(n,j).as_expr()*comb(n,j)*t**j for j in range(n+1)),s.Integer(0)) for n in range(9)]
for n in range(2,9):assert s.expand(Hs[n]-(n-1+x)*(1+t)*Hs[n-1]+(n-1)*(n-2+2*x)*t*Hs[n-2])==0
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],manifest_files_verified=count,root_checks={'actual_n7k2_factorization':True,'quadratic_discriminant':-404,'n17_mixed_defect':str(cross(b(17,0),b(17,7),7)),'n35_artificial_weight':str(w),'n35_artificial_defect':str(negative),'signed_recurrence_n2_through8':True},root_scope='Read complete discovery and summary; independent exact polynomial reconstruction verifies reported obstructions and seven recurrence identities. No universal GIT coefficient inequality, source counterexample, or primary-paper/full-registry audit claimed.',target='Both clauses of Choi–Kiem–Lee2505.01087v2 Conjecture4.10: all odd n, all prescribed k rows and t=1 extraction.',gap='Uniform coefficient Turan inequality preserving the specified parity and triangular weights and controlling subtraction in the recurrence. Arbitrary-mixture failure is not a source refutation.',prior='Worker actual successor-body exclusion of inverse-KL transform target preserved; no new credit.',holds='Published VoR comparison403 and current semantic-registry limits. Latest Omega dce0de1df2fe2e301a5f9d9664ba00eb50f617cd; initial aggregate comparison capped.',instruction_clarification='No Lean/paper was authorized for this research lane; this is an investment gate, not a new general user prohibition.',summary_sha256=hashlib.sha256((lane/'SUMMARY.md').read_bytes()).hexdigest())
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
pn=B/'NEXT.md';txt=pn.read_text().replace('fresh finite/arithmetic r98,','fresh arithmetic/algebraic r100,');txt=txt.replace('independent Chatterjee triangle review r1.','independent Chatterjee triangle review r1. r98 full GIT4.10 remains unresolved; root verified actual nonreal-root row, artificial mixture failure and seven signed recurrence identities. See root-fresh-source-r98-handback/ADOPTION.json.');pn.write_text(txt)
paths=[pn]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve GIT log concavity gap and exact recurrence obstructions','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'manifest_files':count,'root_checks':'PASS','counts':[8,38]}))
