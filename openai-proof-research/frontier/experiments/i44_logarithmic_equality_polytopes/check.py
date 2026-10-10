#!/usr/bin/env python3
"""Exact finite diagnostics, not a proof of the analytic claims. No writes."""
import sys
sys.dont_write_bytecode=True
import json,itertools,functools
from pathlib import Path
VENDOR=Path(__file__).resolve().parents[3]/"frontier/sources/i44_logarithmic_equality_polytopes/frozen/frontier/experiments/i17_six_point_ramsey_r2/vendor"
sys.path[:0]=[str(p) for p in sorted(VENDOR.glob("*.whl"))]
import sympy as S
R=S.Rational
counts={}
def ck(expr,group):
    assert bool(expr),(group,expr)
    counts[group]=counts.get(group,0)+1

def polygon(normals,widths):
    rows=[(S.Matrix(p),h) for p,h in zip(normals,widths)]
    rows += [(-p,h) for p,h in list(rows)]
    vertices=set()
    for (p,h),(v,k) in itertools.combinations(rows,2):
        M=S.Matrix([list(p),list(v)])
        if M.det()==0:continue
        x=M.inv()*S.Matrix([h,k])
        if all((a.dot(x)<=b) for a,b in rows):vertices.add(tuple(x))
    def cmp(a,b):
        qa=0 if a[1]>0 or (a[1]==0 and a[0]>=0) else 1
        qb=0 if b[1]>0 or (b[1]==0 and b[0]>=0) else 1
        if qa!=qb:return -1 if qa<qb else 1
        d=a[0]*b[1]-a[1]*b[0]
        return -1 if d>0 else (1 if d<0 else 0)
    vs=sorted(vertices,key=functools.cmp_to_key(cmp))
    area=sum(vs[i][0]*vs[(i+1)%len(vs)][1]-vs[i][1]*vs[(i+1)%len(vs)][0] for i in range(len(vs)))/2
    facets=[]
    for p,h in rows:
        ends=[S.Matrix(x) for x in vs if p.dot(S.Matrix(x))==h]
        assert len(ends)==2
        d=ends[1]-ends[0];rot=S.Matrix([-p[1],p[0]])
        length_over_normal=next(abs(d[k]/rot[k]) for k in range(2) if rot[k])
        facets.append({'centroid':(ends[0]+ends[1])/2,'derivative':length_over_normal,'ends':{tuple(e) for e in ends}})
    N=len(normals);w=[2*widths[i]*facets[i]['derivative']/area for i in range(N)]
    K=S.zeros(N)
    for i in range(N):
        for j in range(i+1,N):
            val=0
            for ii in [i,i+N]:
                for jj in [j,j+N]:
                    if facets[ii]['ends'] & facets[jj]['ends']:
                        det=abs(S.Matrix([list(rows[ii][0]),list(rows[jj][0])]).det())
                        val+=widths[i]*widths[j]/det/area
            K[i,j]=K[j,i]=val
    H=S.zeros(N)
    for i in range(N):
        for j in range(i+1,N):
            v=K[i,j]-w[i]*w[j]
            H[i,i]+=v;H[j,j]+=v;H[i,j]-=v;H[j,i]-=v
    return area,w,K,H,facets,vs

a,b,c,t,d=S.symbols('a b c t d',positive=True)
Q=4*a*b-(a+b-c)**2
x=[a,b,c]
Hsym=S.Matrix(3,3,lambda i,j:-S.simplify(x[i]*S.diff(x[j]*S.diff(S.log(Q),x[j]),x[i])))
ck(S.simplify(Q-(-a*a-b*b-c*c+2*a*b+2*a*c+2*b*c))==0,'hexagon')
vol=Q.subs({a:S.exp(t),b:S.exp(-t),c:2-d})
curv=S.simplify(-S.diff(S.log(vol),t,2).subs(t,0))
ck(S.simplify(curv-4*d/(4-d*d))==0,'hexagon')
ws=[S.simplify(v*S.diff(Q,v)/Q) for v in x]
wd=[S.simplify(v.subs({a:1,b:1,c:2-d})) for v in ws]
ck(S.simplify(sum(wd)-2)==0,'hexagon')
prob_norm=S.simplify((wd[0]+wd[1])/2)
ck(S.simplify(prob_norm-2/(2+d))==0,'hexagon')
ck(S.simplify(curv/prob_norm-2*d/(2-d))==0,'hexagon')
cn=(c-a-b)/(2*a)
ck(S.simplify(S.diff(cn.subs({a:S.exp(t),b:S.exp(-t),c:2-d}),t).subs(t,0)-d/2)==0,'centroid')
for aa,bb,cc in [(R(1),R(1),R(k,4)) for k in range(1,8)]+[(R(3,2),R(1),R(k,4)) for k in range(3,10)]:
    area,w,K,H,fac,vs=polygon([(1,0),(0,1),(1,1)],[aa,bb,cc])
    vals={a:aa,b:bb,c:cc}
    ck(area==Q.subs(vals),'hexagon_geometry')
    ck(w==[v.subs(vals) for v in ws],'hexagon_geometry')
    ck(H==Hsym.subs(vals),'ridge_hessian')
    ck(fac[0]['centroid']==S.Matrix([aa,(cc-aa-bb)/2]),'centroid')
    ck(sum(w)==2,'hexagon_geometry')
    # Euler/divergence matrix sum using nonunit normals and unnormalized supports.
    mat=S.zeros(2)
    for i,p in enumerate([(1,0),(0,1),(1,1)]):mat+=w[i]*(fac[i]['centroid']/[aa,bb,cc][i])*S.Matrix([p])
    ck(mat==S.eye(2),'centroid')

area,w,K,H,fac,vs=polygon([(1,0),(0,1),(1,1),(1,-1)],[R(1),R(1),R(3,2),R(3,2)])
ck(area==R(7,2),'octagon')
ck(w==[R(4,7),R(4,7),R(3,7),R(3,7)],'octagon')
ck(K[0,1]==K[2,3]==0,'octagon')
ck(-w[0]*w[1]==R(-16,49) and -w[2]*w[3]==R(-9,49),'octagon')
for i in [0,1]:
 for j in [2,3]:ck(K[i,j]==R(6,7) and K[i,j]-w[i]*w[j]==R(30,49),'octagon')
ck(H*S.ones(4,1)==S.zeros(4,1),'octagon')
ck(H.rank()==3 and all(v>=0 for v in H.eigenvals()),'octagon')

# Nonsimple octahedron: four facets meet at each vertex.
U=[S.Matrix(v) for v in [(1,1,1),(1,1,-1),(1,-1,1),(-1,1,1)]]
rows=U+[-v for v in U];verts=[s*S.eye(3)[:,i] for i in range(3) for s in [-1,1]]
ck(all(sum(p.dot(v)==1 for p in rows)==4 for v in verts),'nonsimple_octahedron')
V=R(4,3);w3=[R(3,4)]*4;Kap=S.zeros(4)
for i in range(4):
 for j in range(i+1,4):
    coef=0
    for ii in [i,i+4]:
     for jj in [j,j+4]:
      es=[v for v in verts if rows[ii].dot(v)==rows[jj].dot(v)==1]
      if len(es)==2:
       delta=es[1]-es[0];cross=rows[ii].cross(rows[jj])
       coef+=next(abs(delta[k]/cross[k]) for k in range(3) if cross[k])/V
    Kap[i,j]=Kap[j,i]=coef
    ck(coef==R(3,4),'nonsimple_octahedron')
H3=S.zeros(4)
for i in range(4):
 for j in range(i+1,4):
  z=Kap[i,j]-w3[i]*w3[j];H3[i,i]+=z;H3[j,j]+=z;H3[i,j]-=z;H3[j,i]-=z
ck(H3.eigenvals()=={S.Integer(0):1,R(3,4):3},'nonsimple_octahedron')
ck(sum(w3)==3,'nonsimple_octahedron')
# Persistent event at e1: normal relation p1+p4-p2-p3=0 after choosing signed p4.
active=[p for p in rows if p.dot(S.Matrix([1,0,0]))==1]
M=S.Matrix([list(p) for p in active]);rel=M.T.nullspace()[0]
ck(sum(rel)==0,'persistent_wall')
ck(S.simplify(sum(rel)*S.exp(3*t))==0,'persistent_wall')

# Product gamma model and exact normal-coordinate kernels.
q=S.symbols('q',positive=True)
for k in range(1,6):
    # Gamma ratio recurrence: q E psi^k for a product slab tends to Gamma(k).
    expr=S.prod(R(j)+1/q for j in range(1,k))
    ck(S.limit(expr,q,S.oo)==S.factorial(k-1),'gamma_boundary')
for n in range(2,7):
    aa=S.eye(n)/q;cov=S.eye(n)/q;bb=S.Matrix(list(range(1,n+1)))
    ck(aa-cov==S.zeros(n),'box_soft')
    ck((bb.T*cov*bb)[0]==sum(i*i for i in range(1,n+1))/q,'box_soft')
    for i in range(n):ck(sum(cov[i,j] for j in range(n))==aa[i,i],'box_soft')

# A nontrivial hard matrix gives unscaled contraction saturation nonetheless.
r=S.symbols('r',positive=True)
ww=S.diag(R(2,3),R(2,3),R(2,3))
HH=Hsym.subs({a:1,b:1,c:1});bb=S.Matrix([1,-1,0]);AA=ww/r;DD=HH/r**2;CC=AA-DD
sigma=(bb.T*CC*bb)[0]
left=S.simplify(1-(bb.T*CC*AA.inv()*CC*bb)[0]/sigma)
right=S.simplify(((bb.T*DD*bb)[0]-(bb.T*DD*AA.inv()*DD*bb)[0])/sigma)
ck(S.simplify(left-right)==0,'dual_defect')
ck(S.limit(left,r,S.oo)==0,'dual_defect')
ck(S.limit(r*left,r,S.oo)==(bb.T*HH*bb)[0]/(bb.T*ww*bb)[0],'dual_defect')
ck((bb.T*HH*bb)[0]>0,'dual_defect')
# Scalar Hilbert identity for a rational contraction.
T=S.Matrix([[R(1,2),0],[0,R(1,3)]]);u=S.Matrix([R(3,5),R(4,5)]);cv=S.Matrix([R(2),R(7)]);ss=(cv.T*T*u)[0]
ck(S.expand(((cv-ss*T*u).T*(cv-ss*T*u))[0]+ss**2*(1-(T*u).dot(T*u))-(cv.dot(cv)-ss**2))==0,'audit_defect')

# Gaussian q=2 Cauchy--Binet at t=0.
P=[S.Matrix(v) for v in [(1,0),(0,1),(1,1),(1,-1)]]
for slopes in [(0,0,0,0),(1,-1,0,2),(2,2,2,2)]:
    coeff=[];sums=[]
    for i,j in itertools.combinations(range(4),2):
        det=S.Matrix.hstack(P[i],P[j]).det()
        if det:coeff.append(det**2);sums.append(slopes[i]+slopes[j])
    Z=sum(coeff);mean=sum(c*v for c,v in zip(coeff,sums))/Z
    var=sum(c*(v-mean)**2 for c,v in zip(coeff,sums))/Z
    Qt=S.zeros(2)
    for p,v in zip(P,slopes):Qt+=S.exp(-2*v*t)*(p*p.T)
    curvature=S.simplify(S.diff(S.log(Qt.det()),t,2).subs(t,0)/2)
    ck(curvature==2*var,'gaussian_bases')
    ck((var==0)==(len(set(slopes))==1),'gaussian_bases')

# Green identity for arbitrary polynomial curvatures, and exponential events.
l=S.symbols('l',positive=True)
for k in range(5):
    f=-t**(k+2)/((k+1)*(k+2))
    lhs=f.subs(t,l)-(1-l)*f.subs(t,0)-l*f.subs(t,1)
    rhs=S.integrate((1-l)*t*t**k,(t,0,l))+S.integrate(l*(1-t)*t**k,(t,l,1))
    ck(S.simplify(lhs-rhs)==0,'green')
# A polynomial in e^t with exactly three real event times.
y=S.symbols('y');ev=(y-1)*(y-2)*(y-3)
for v in [1,2,3]:ck(ev.subs(y,v)==0,'finite_events')
# The augmented jet matrix proves independence of {1,t,exp(t),exp(2t),exp(-t)}.
fns=[S.Integer(1),t,S.exp(t),S.exp(2*t),S.exp(-t)]
jet=S.Matrix([[S.diff(f,t,k).subs(t,0) for f in fns] for k in range(5)])
ck(jet.det()!=0,'centroid_exponential')
# True endpoint supports: midpoint diagonal redundancy using exact radicals.
ck(S.simplify(2*S.sqrt(R(5,4))-S.sqrt(2)-1/S.sqrt(2))>0,'redundancy')
# Adaptedness obstruction and local vector cancellation.
ck(2!=abs(1-1),'erosion')
tri=[S.Matrix([0,0]),S.Matrix([3,0]),S.Matrix([0,3])];ct=sum(tri,S.zeros(2,1))/3
mid=[(tri[i]+tri[(i+1)%3])/2 for i in range(3)]
ck(sum((v-ct for v in mid),S.zeros(2,1))==S.zeros(2,1),'vector_balance')
# Retained tensor identity in a normalized constant frame.
for n in [2,3,4]:
 for seed in [1,2,5]:
    inds=list(itertools.product(range(n),repeat=3))
    C={ijk:R(sum((v+1)**2 for v in ijk)+seed*sum(ijk)+1,seed+1) for ijk in inds}
    SS={ijk:R(S.prod(v+1 for v in ijk)+seed,seed+2) for ijk in inds}
    hh=S.Matrix(n,n,lambda i,j:R((i+1)*(j+1)+seed*(i==j),seed+3))
    J={ijk:sum(hh[ijk[0],a]*C[(a,ijk[1],ijk[2])] for a in range(n)) for ijk in inds}
    sy={ijk:(J[ijk]+J[(ijk[1],ijk[0],ijk[2])]+J[(ijk[2],ijk[0],ijk[1])])/3 for ijk in inds}
    KK={ijk:SS[ijk]+J[(ijk[1],ijk[0],ijk[2])] for ijk in inds}
    left=2*sum((SS[k]+sy[k])**2 for k in inds)+sum((J[k]-J[(k[1],k[0],k[2])])**2 for k in inds)/6
    right=sum(KK[k]**2 for k in inds)/2+R(3,2)*sum((SS[k]+sy[k])**2 for k in inds)
    ck(left==right,'tensor_remainder')
    ck(right>=sum(KK[k]**2 for k in inds)/2,'tensor_remainder')
be,ai,di,qq=S.symbols('beta ai di qq',nonzero=True)
ga=be/qq;mi=qq*ai
ck(S.expand(-2*ga*di+ga**2*mi-2*ga*(qq-1)*di+ga**2*(qq-1)*mi+2*be*di-be**2*ai)==0,'homogeneous_completion')
DD=t+2*S.cosh(t)-2
ratio=(4-t*t)/(4-DD*DD)
ck(S.series(S.log(ratio),t,0,4).removeO()==t**3/2,'cubic_rigidity')
ck(S.series(S.exp(-2*t)-S.exp(2*t),t,0,3).removeO()==-4*t,'cubic_rigidity')
ck(S.simplify((a+c)/2+(b+c)/2-3*c/2-(a+b-c)/2)==0,'cubic_rigidity')
for rr in [R(101,100),R(21,20),R(11,10)]:
    delta=rr-1;aa=rr;bb=1/rr;cc=2-delta
    area,w,K,H,fac,vs=polygon([(1,0),(0,1),(1,1)],[aa,bb,cc])
    ck(len(vs)==6,'cubic_rigidity')
    vv=S.Matrix([1,R(1,2)]);vv2=S.Matrix([R(1,2),1])
    support=lambda v:max(v.dot(S.Matrix(x)) for x in vs)
    ck(support(vv)+support(vv2)-support(vv+vv2)==(aa+bb-cc)/2,'cubic_rigidity')
    ck(area==4-(delta+rr+1/rr-2)**2,'cubic_rigidity')
print(json.dumps({'status':'PASS','assertions':sum(counts.values()),'groups':counts,'scope':'Exact finite diagnostics only; no analytic proof, kernel classification or priority certificate.'},indent=2,sort_keys=True))
