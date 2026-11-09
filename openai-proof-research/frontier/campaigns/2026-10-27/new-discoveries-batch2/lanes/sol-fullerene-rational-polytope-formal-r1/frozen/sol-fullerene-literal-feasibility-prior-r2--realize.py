from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json
L=Path(__file__).parent
S=L/'frozen/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fullerene-heat-trace-breadth-depth-r286'
def solve(A,B):
    n=len(A);a=[[F(x) for x in A[i]+B[i]] for i in range(n)]
    for k in range(n):
        j=next(j for j in range(k,n) if a[j][k]);a[k],a[j]=a[j],a[k]
        v=a[k][k];a[k]=[x/v for x in a[k]]
        for j in range(n):
            if j!=k:
                v=a[j][k]
                if v:a[j]=[x-v*y for x,y in zip(a[j],a[k])]
    return [x[n:] for x in a]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return [x-y for x,y in zip(a,b)]
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def run(name):
    edges=json.loads((S/f'{name}-edges.json').read_text());faces=json.loads((S/'graph-certificates.json').read_text())[name]['faces']
    adj=[set() for _ in range(32)]
    for i,j in edges:adj[i].add(j);adj[j].add(i)
    outer=faces[0];inside=[i for i in range(32) if i not in outer];xy={outer[0]:[F(0),F(0)],outer[1]:[F(1),F(0)],outer[2]:[F(0),F(1)]}
    A=[[len(adj[i]) if i==j else -int(j in adj[i]) for j in inside] for i in inside]
    B=[[sum(xy[j][k] for j in adj[i] if j in xy) for k in range(2)] for i in inside]
    xy.update(zip(inside,solve(A,B)))
    stress={tuple(sorted(e)):F(1) for e in edges}
    oe=list(combinations(outer,2));eq=[];rhs=[]
    for i in outer:
        for k in range(2):
            eq.append([xy[next(v for v in e if v!=i)][k]-xy[i][k] if i in e else 0 for e in oe])
            rhs.append([-sum(xy[j][k]-xy[i][k] for j in adj[i] if j not in outer)])
    # choose an independent subsystem; verify every equilibrium equation afterwards
    for rows in combinations(range(6),3):
        try:w=solve([eq[r] for r in rows],[rhs[r] for r in rows]);break
        except (StopIteration,ZeroDivisionError):continue
    for e,v in zip(oe,w):stress[tuple(sorted(e))]=v[0]
    for i in range(32):
        for k in range(2):assert sum(stress[tuple(sorted((i,j)))]*(xy[j][k]-xy[i][k]) for j in adj[i])==0
    darts={(f[k],f[(k+1)%3]):t for t,f in enumerate(faces) for k in range(3)}
    planes={0:[F(0)]*3};todo=[0]
    while todo:
        t=todo.pop();f=faces[t]
        for k in range(3):
            i,j=f[k],f[(k+1)%3];u=darts[j,i];dx,dy=sub(xy[j],xy[i]);w=stress[tuple(sorted((i,j)))]
            new=[a+w*b for a,b in zip(planes[t],[dy,-dx,dx*xy[i][1]-dy*xy[i][0]])]
            if u in planes:assert planes[u]==new
            else:planes[u]=new;todo.append(u)
    pts=[]
    for i in range(32):
        zs={dot(planes[t],xy[i]+[F(1)]) for t,f in enumerate(faces) if i in f};assert len(zs)==1
        pts.append(xy[i]+[zs.pop()])
    # Independent supporting-plane check; enumerate ALL triples to certify no other facets.
    supports=[]
    for f in combinations(range(32),3):
        n=cross(sub(pts[f[1]],pts[f[0]]),sub(pts[f[2]],pts[f[0]]))
        if not any(n):continue
        ds=[dot(n,sub(p,pts[f[0]])) for p in pts]
        if min(ds)>=0 or max(ds)<=0:
            assert {i for i,d in enumerate(ds) if not d}==set(f)
            supports.append(f)
    assert set(supports)=={tuple(sorted(f)) for f in faces}
    # Translate by positive barycenter; polarity gives primal vertices from supporting planes.
    center=[sum(p[k] for p in pts)/32 for k in range(3)];q=[sub(p,center) for p in pts];pv=[]
    for f in faces:
        n=cross(sub(q[f[1]],q[f[0]]),sub(q[f[2]],q[f[0]]));c=dot(n,q[f[0]])
        if c<0:n=[-x for x in n];c=-c
        assert c>0 and all(dot(n,p)<=c for p in q)
        pv.append([x/c for x in n])
    # Every non-singular triple of primal defining planes: feasible iff listed vertex.
    feasible=set()
    for tri in combinations(range(32),3):
        try:v=[x[0] for x in solve([q[i] for i in tri],[[1],[1],[1]])]
        except StopIteration:continue
        if all(dot(p,v)<=1 for p in q):feasible.add(tuple(v))
    assert feasible=={tuple(v) for v in pv} and len(feasible)==60
    incidence=[[j for j,v in enumerate(pv) if dot(p,v)==1] for p in q]
    assert sorted(map(len,incidence))==[5]*12+[6]*20
    assert {tuple((i,j)) for i,j in combinations(range(32),2) if len(set(incidence[i])&set(incidence[j]))==2}=={tuple(sorted(e)) for e in edges}
    return {'dual_vertices':q,'dual_facets':faces,'primal_vertices':pv,'primal_facets':incidence,'all_support_triples':len(supports),'all_feasible_triple_vertices':len(feasible),'max_fraction_bits':max(max(x.numerator.bit_length(),x.denominator.bit_length()) for p in q+pv for x in p)}
out={n:run(n) for n in ['G','H']}
(L/'rational-realizations.json').write_text(json.dumps(out,default=str,indent=2))
print(json.dumps({n:{k:v for k,v in d.items() if isinstance(v,int)} for n,d in out.items()}))
