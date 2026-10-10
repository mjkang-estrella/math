#!/usr/bin/env python3
"""Independent finite diagnostics from actual zonotope vertices; no analytic certificate."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import itertools, json
R = Path(__file__).resolve().parents[3]
S = R / 'frontier/sources/i47_planar_logarithmic_stability_r2'
vendor = S / 'frozen/frontier/sources/i46_quantitative_logarithmic_stability/vendor'
sys.path[:0] = [str(p) for p in sorted(vendor.glob('*.whl'))]
import sympy as sp
Q = sp.Rational
checks = 0

def ck(x):
    global checks
    assert bool(x), x
    checks += 1

def cross(a,b):
    return a[0]*b[1]-a[1]*b[0]

def hull(points):
    points=sorted(set(tuple(p) for p in points))
    def half(seq):
        out=[]
        for p in seq:
            while len(out)>1 and cross(sp.Matrix(out[-1])-sp.Matrix(out[-2]),sp.Matrix(p)-sp.Matrix(out[-1]))<=0:
                out.pop()
            out.append(p)
        return out
    return [sp.Matrix(p) for p in half(points)[:-1]+half(points[::-1])[:-1]]

def area(poly):
    return sum(cross(a,b) for a,b in zip(poly,poly[1:]+poly[:1]))/2

def support(poly,u):
    return max(u.dot(p) for p in poly)

def unit(t):
    return sp.Matrix([(1-t*t)/(1+t*t),2*t/(1+t*t)])

def psd(A,strict=False):
    ck(A==A.T)
    while A.rows:
        pivot=A[0,0]
        ck(pivot>0 if strict else pivot>=0)
        if pivot==0:
            ck(all(A[0,j]==0 for j in range(A.cols)))
            A=A[1:,1:]
        else:
            A=A[1:,1:]-A[1:,0]*A[0,1:]/pivot

def slab_vertices(normals,widths):
    signed=[(u,h) for u,h in zip(normals,widths)]+[(-u,h) for u,h in zip(normals,widths)]
    out=[]
    for (u,h),(v,k) in itertools.combinations(signed,2):
        B=sp.Matrix.vstack(u.T,v.T)
        if not B.det(): continue
        x=B.inv()*sp.Matrix([h,k])
        if all(w.dot(x)<=a for w,a in signed): out.append(x)
    return hull(out)

sets=[[Q(0),Q(1)], [Q(0),Q(1,2),Q(2)],
      [Q(0),Q(1,1000),Q(1),Q(1000)],
      [Q(0),Q(1,7),Q(1,2),Q(1),Q(3)],
      [Q(0),Q(1,11),Q(1,3),Q(2,3),Q(1),Q(2),Q(7)]]
rot=sp.Matrix([[Q(3,5),-Q(4,5)],[Q(4,5),Q(3,5)]])
cases=[]
for ts in sets:
    for mode in range(3):
        us=[(rot if mode==2 else sp.eye(2))*unit(t) for t in ts]
        n=len(us)
        masses=sp.Matrix([Q(i+1,3) if mode==0 else (Q(1,10**8) if i%2 else Q(2+i)) for i in range(n)])
        generators=[sp.Matrix([-u[1],u[0]])*masses[i]/4 for i,u in enumerate(us)]
        vertices=hull([sum((sg*g for sg,g in zip(signs,generators)),sp.zeros(2,1)) for signs in itertools.product([-1,1],repeat=n)])
        ck(len(vertices)==2*n)
        V=area(vertices); h=sp.Matrix([support(vertices,u) for u in us])
        A=sp.Matrix(n,n,lambda i,j:abs(cross(us[i],us[j]))/4)
        ck(h==A*masses);ck(V==h.dot(masses)/2)
        # Recover the actual paired edge lengths from exposed vertex pairs.
        edge_order=[]
        for v,w in zip(vertices,vertices[1:]+vertices[:1]):
            found=[]
            for i,u in enumerate(us):
                for sign in [-1,1]:
                    if (sign*u).dot(v)==h[i] and (sign*u).dot(w)==h[i]: found.append((i,sign))
            ck(len(found)==1);edge_order.append(found[0])
        for i,u in enumerate(us):
            ev=[v for v in vertices if u.dot(v)==h[i]]
            ck(len(ev)==2);ck(4*(ev[1]-ev[0]).dot(ev[1]-ev[0])==masses[i]**2)
        for t in [Q(-3),Q(-1,5),Q(1,19),Q(2,5),Q(9)]:
            u=unit(t)
            ck(support(vertices,u)==sum(abs(cross(u,w))*m/4 for w,m in zip(us,masses)))
        # Build the support-area quadratic directly from intersecting adjacent facet lines.
        X=sp.symbols('x:'+str(n)); symbolic=[]
        for (i,si),(j,sj) in zip(edge_order[-1:]+edge_order[:-1],edge_order):
            B=sp.Matrix.vstack((si*us[i]).T,(sj*us[j]).T)
            symbolic.append(B.inv()*sp.Matrix([X[i],X[j]]))
        Vpoly=sp.expand(area(symbolic)); subs=dict(zip(X,h))
        ck(Vpoly.subs(subs)==V)
        C=sp.hessian(Vpoly,X)
        ck(C*h==masses);ck(C*A==sp.eye(n))
        nu=sp.Matrix([h[i]*masses[i]/(2*V) for i in range(n)])
        N=sp.diag(*nu);T=sp.diag(*[1/x for x in h])*A*sp.diag(*masses)
        ck(sum(nu)==1);ck(T*sp.ones(n,1)==sp.ones(n,1));ck(N*T==T.T*N)
        # Exact logarithmic Hessian from the independent vertex-area polynomial.
        H=-(sp.diag(*h)*C*sp.diag(*h)+sp.diag(*[h[i]*masses[i] for i in range(n)]))/V+4*nu*nu.T
        ck(H==-2*N*T.inv()-2*N+4*nu*nu.T)
        E=2*N*(sp.eye(n)+T)-4*nu*nu.T
        psd(H);psd(E);psd(H-E)
        B=sp.zeros(n,n-1)
        for j in range(n-1): B[j,j]=1;B[n-1,j]=-nu[j]/nu[n-1]
        psd(-B.T*N*T*B,strict=True)
        slopes=[sp.Matrix([(-1)**i*(i+1) for i in range(n)]),sp.Matrix([10**9 if i==n-1 else -i for i in range(n)]),sp.ones(n,1)*7]
        for b in slopes:
            q=b-sp.ones(n,1)*nu.dot(b)
            ck(nu.dot(T.inv()*q)==0)
            J=sum((N*T)[i,j]*(q[i]+q[j])**2 for i in range(n) for j in range(n))
            ck((b.T*H*b)[0]>=J);ck((b.T*E*b)[0]==J)
        if n==2:
            ck(T==sp.Matrix([[0,1],[1,0]]));ck(H==sp.zeros(2));ck(nu==sp.ones(2,1)/2)
        cases.append({'directions':n,'mode':mode,'vertices':len(vertices),'area':str(V)})

# Persistent and changing redundancy: the diagonal is true at both endpoints
# but inactive on an open interval around the midpoint.
norms=[sp.Matrix([1,0]),sp.Matrix([0,1]),sp.Matrix([1,1])]
K=slab_vertices(norms,[1,4,Q(41,10)]);L=slab_vertices(norms,[4,1,Q(41,10)])
P=slab_vertices(norms,[2,2,Q(41,10)])
ck(len(K)==len(L)==6);ck(len(P)==4);ck(area(P)==16)
ck(support(P,norms[2])==4);ck(support(K,norms[2])==Q(41,10))
for a in [Q(8,5),Q(5,2)]: ck(a+4/a==Q(41,10))
for t in [Q(-3),Q(-1),Q(0),Q(1,5),Q(1,2),Q(1),Q(2),Q(8)]:
    u=unit(t)
    ck(support(P,u)**2<=support(K,u)*support(L,u))

# A union normal that is a facet only at one endpoint still has its actual endpoint support.
K=slab_vertices(norms,[1,1,2]);L=slab_vertices(norms,[1,1,Q(3,2)])
ck(len(K)==4 and len(L)==6)
ck(support(K,norms[2])==2 and support(L,norms[2])==Q(3,2))

# Oblique common-block comparison: exact geometric-mean area identity.
norms=[sp.Matrix([1,0]),sp.Matrix([Q(3,5),Q(4,5)])]
Q0=slab_vertices(norms,[1,4]);Q1=slab_vertices(norms,[9,1]);Qt=slab_vertices(norms,[3,2])
ck(area(Qt)**2==area(Q0)*area(Q1));ck(area(Qt)==4*3*2/Q(4,5))

# Triangle-square estimate with unrestricted real values, including large signs.
a,b,c=sp.symbols('a b c',real=True)
F=3*((a+b)**2+(a+c)**2+(b+c)**2)-4*a*a
psd(sp.hessian(F,(a,b,c))/2)
ck(sp.expand(2*a-((a+b)+(a+c)-(b+c)))==0)

# Fourier negative form: constant-mode elimination, checked algebraically.
p,u,v,w=sp.symbols('p u v w',positive=True)
ck(sp.expand((v*v-(u*v/p)**2)-(1-u*u/(p*p))*v*v)==0)
# Exact cap triangle: cross-section integration equals r eta^2/H.
r,eta,H,z=sp.symbols('r eta H z',positive=True)
ck(sp.integrate(2*r*z/H,(z,0,eta))==r*eta**2/H)

# Radial homogeneous Gamma factors; test several n,q and moment degrees.
for n in [2,3,5]:
    for q in [2,4,10]:
        for degree in [0,2]:
            ck(sp.simplify(Q(n+degree,q)*sp.gamma(Q(n+degree,q))-sp.gamma(1+Q(n+degree,q)))==0)
# Nonzero soft chord slope on a product density: EF cannot be discarded.
for slopes in [(2,3),(-7,2),(1,1)]:
    for q in [2,4,12]:
        mean=sum(-q*Q(b,q) for b in slopes)
        ck(mean==-sum(slopes));ck(mean!=0)
        ck(sum((q*b)**2*(Q(1,q)-Q(1,q)) for b in slopes)==0)

# Conditional self-adjoint normalization, with an oblique perturbation.
Hhalf=sp.diag(2,3,5);A=sp.Matrix([[2,Q(1,100),0],[0,3,1],[0,0,3]])
H=Hhalf**2;B=Hhalf.inv()*A*Hhalf
ck(B-B.T==Hhalf.inv()*(A*H-H*A.T)*Hhalf.inv())
Bs=(B+B.T)/2;ck(Bs==Bs.T)

t=sp.symbols('t')
hex_def=sp.log((4-t*t)/(4-(t+2*sp.cosh(t)-2)**2))
ck(sp.series(hex_def,t,0,5).removeO()==t**3/2+t**4/4)
ck(1-4*Q(1,5)==Q(1,5));ck(Q(1,5)/2==Q(1,10))
print(json.dumps({'status':'PASS','exact_assertions':checks,'genuine_zonotope_cases':len(cases),
 'cases':cases,'scope':'Independent finite rational/symbolic diagnostics, not a proof of the analytic estimates or significance.'},indent=2,sort_keys=True))
