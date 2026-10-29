from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
import sympy as s
root=Path(__file__).resolve().parent;B=root.parents[1];repo=B.parents[4];lane=root.parent/'sol-fresh-source-discovery-r96'
nmanifest=0
for line in (lane/'manifest.sha256').read_text().splitlines():
    h,n=line.split(maxsplit=1);assert hashlib.sha256((lane/n.strip()).read_bytes()).hexdigest()==h,n;nmanifest+=1
x=s.symbols('x');T=x+1
C1,D1,H1=6+6*x,3+3*x,1+4*x
C2,D2,H2=1+5*x,6+x,1+3*x
C=s.expand(C1*(D2+T*H2)+(D1+T*H1)*C2)
D=s.expand(D1*D2+T*H1*H2)
H=s.expand(D1*H2+H1*D2+x*H1*H2)
U=s.expand(C+T*H)
def coeff(p):return [int(s.expand(p).coeff(x,i)) for i in range(s.degree(p,x)+1)]
def lc(a):return all(a[i]**2>=a[i-1]*a[i+1] for i in range(1,len(a)-1))
assert coeff(C)==[46,100,92,38] and coeff(D)==[19,29,22,12]
assert coeff(H)==[9,38,20,12] and 20**2-38*12==-56
assert coeff(U)==[55,147,150,70,12] and lc(coeff(U))
for a,b,h in [(C1,D1,H1),(C2,D2,H2)]:
    assert all(lc(coeff(p)) for p in (a,b,h,a+T*h))
    assert all(v>=0 for v in coeff(a-h))
c1,c2,h1,h2=s.symbols('c1 c2 h1 h2')
assert s.expand(c1*c2+T*h1*h2-(c1*h2+h1*c2+x*h1*h2)-(c1-h1)*(c2-h2))==0
record=dict(utc=datetime.now(timezone.utc).isoformat(),decision='UNRESOLVED_NO_NOMINATION',credit=0,counts=[8,38],manifest_files_verified=nmanifest,root_validation={'parallel_state':[coeff(C),coeff(D),coeff(H)],'H_degree2_defect':-56,'U_coefficients':coeff(U),'U_logconcave':True,'series_difference_identity':True},scope='Root read full discovery and summary. Independently reconstructed polynomial parallel operation and series difference identity. No claim of graph realization of artificial inputs, no root verification of motivic stratification from primary bodies, no universal graph theorem.',target='Aluffi–Marcolli–Qaisar all-melonic Kirchhoff-complement coefficient log-concavity, published Conjecture3.1; arbitrary construction depth.',gap='A stronger graph-realizable invariant or direct-U mixed coefficient estimate preserved under both operations. Artificial state-cone failure does not refute source; U itself remains LC.',prior='Worker reads public gamma-to-h LC proof and exact Chen ULC-failure proof claim. Preserve distinctions between inspected public claim and independently certified theorem.',freshness='c80e3a31a64948bb3c8b407f9881aaf5b96d63b6; short delta7commits3files, old baseline97commits300files capped. No comprehensive current clearance.',summary_sha256=hashlib.sha256((lane/'SUMMARY.md').read_bytes()).hexdigest())
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';txt=p.read_text().replace('fresh finite/arithmetic r96,','fresh finite/arithmetic r98,');txt=txt.replace('fresh analytic/geometric r97.','fresh analytic/geometric r97. r96 all-melonic log-concavity remains unresolved; root verified manifest and exact artificial state-cone obstruction, with U still log-concave. See root-fresh-source-r96-handback/ADOPTION.json.');p.write_text(txt)
paths=[p]
for folder in (root,lane):paths.extend(q for q in folder.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name!='commit-paths.txt' and q.suffix not in ('.pyc','.olean','.ilean'))
spec=root/'commit-paths.txt';spec.write_text('\n'.join(str(q.relative_to(repo)) for q in sorted(set(paths)))+'\n')
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['commit','--quiet','-m','Preserve melonic log concavity gap and exact state obstruction','--pathspec-from-file='+str(spec)],cwd=repo,check=True)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps({'manifest_files':nmanifest,'root_checks':'PASS','counts':[8,38]}))
