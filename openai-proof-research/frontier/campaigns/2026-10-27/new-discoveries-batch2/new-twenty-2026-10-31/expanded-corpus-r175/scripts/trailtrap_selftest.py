import sys,pathlib,itertools,io,contextlib
sys.path.insert(0,str(pathlib.Path(__file__).parent))
import trailtrap as T
def run(name,nv,E,expect):
    with contextlib.redirect_stdout(io.StringIO()): r=T.solve(nv,E)
    got='P2' if all(x[1] for x in r) else 'P1'
    print(name,'got',got,'expected',expect,'OK' if got==expect else 'MISMATCH')
K=lambda n:[(a,b) for a,b in itertools.combinations(range(n),2)]
Kb=lambda p,q:[(a,p+b) for a in range(p) for b in range(q)]
run('K4',4,K(4),'P1'); run('K13',4,Kb(1,3),'P1'); run('K33',6,Kb(3,3),'P2'); run('K35',8,Kb(3,5),'P1')
run('K5',5,K(5),'P2' if False else '?'); run('K6',6,K(6),'P1')
for n in (3,5,7): nv,E=T.grid(2,n); run('P2xP%d'%n,nv,E,'P1' if n>3 else '?')
