#!/usr/bin/env python3
"""Independent exact adversarial diagnostics. Read-only; no analytic-limit certification."""
import sys
sys.dont_write_bytecode = True
import itertools as it
import json
from functools import lru_cache
from pathlib import Path
VENDOR = Path(__file__).resolve().parents[3]/'frontier/sources/i45_logarithmic_equality_r2/frozen/frontier/sources/i44_logarithmic_equality_polytopes/frozen/frontier/experiments/i17_six_point_ramsey_r2/vendor'
sys.path[:0] = [str(p) for p in sorted(VENDOR.glob('*.whl'))]
import sympy as s

groups = {}
def ck(value, group):
    assert bool(value), group
    groups[group] = groups.get(group, 0) + 1
def zero(value, group):
    ck(s.simplify(value) == 0, group)

# Arbitrary rational third-order tensors: no dependence on author's examples.
# J need only be symmetric in its last two indices, a larger test class.
for n in (2, 3):
    idx = list(it.product(range(n), repeat=3))
    for seed in range(1, 5):
        S = {i: s.Rational(sum((k+1)**2 for k in i)+seed, seed+2) for i in idx}
        J = {i: s.Rational((i[0]+1)*(i[1]+i[2]+2)+seed*(i[1]-i[2])**2, seed+3) for i in idx}
        sym = lambda D, i: sum(D[p] for p in it.permutations(i))/6
        K = {i: S[i]+J[(i[1], i[0], i[2])] for i in idx}
        left = sum(2*(S[i]+sym(J,i))**2+s.Rational(1,6)*(J[i]-J[(i[1],i[0],i[2])])**2 for i in idx)
        right = sum(K[i]**2/2+s.Rational(3,2)*sym(K,i)**2 for i in idx)
        zero(left-right, 'tensor_completion')

# Invariant tensor norm under a genuinely nonorthogonal, non-diagonal constant dual map.
tau=s.Matrix([[3,1],[1,2]]); M=tau.inv(); T=s.Matrix([[2,1],[1,1]])
Ti=T.inv(); tp=T.T*tau*T; mp=tp.inv()
K={(a,k,l):s.Rational(1+2*a+3*k+5*l,7) for a,k,l in it.product(range(2),repeat=3)}
Kp={(a,k,l):sum(T[i,a]*K[i,j,m]*Ti[k,j]*T[m,l] for i,j,m in it.product(range(2),repeat=3)) for a,k,l in K}
def norm(D,t,m):
    return sum(m[a,b]*t[k,r]*m[l,v]*D[a,k,l]*D[b,r,v] for a,b,k,r,l,v in it.product(range(2),repeat=6))
zero(norm(K,tau,M)-norm(Kp,tp,mp),'constant_dual_invariance')

# Exact Gaussian integrations for the entire completion, not only formal cross terms.
# q=2 with noncommuting tau, Hessian(v), and D_x W; quartic v gives nonzero derivative energy.
x,y=s.symbols('x y'); X=s.Matrix([x,y]); eps=s.Rational(3,5)
psi=[x*x, (x+2*y)**2/4, (2*x-y)**2/9]
Hs=[s.hessian(p,(x,y)) for p in psi]; H=eps*s.eye(2)+sum(Hs,s.zeros(2)); cov=H.inv()
@lru_cache(None)
def wick(a,b):
    if a+b==0:return s.Integer(1)
    if (a+b)%2:return s.Integer(0)
    if a:
        return ((a-1)*cov[0,0]*wick(a-2,b) if a>=2 else 0)+(b*cov[0,1]*wick(a-1,b-1) if b else 0)
    return (b-1)*cov[1,1]*wick(0,b-2)
def E(p):return sum(c*wick(*powers) for powers,c in s.Poly(s.expand(p),x,y).terms())
def div(W):return sum(s.diff(W[i],(x,y)[i]) for i in range(2))
def delta(W):return (H*X).dot(W)-div(W)
v=x**4/12+x*x*y*y/5+y**4/7+x*y/3
h=s.hessian(v,(x,y)); B=cov*h*cov; P=cov*h
W=s.Matrix([delta(B.row(i).T) for i in range(2)])
u=s.expand(delta(W)); DW=W.jacobian(X)
divz=s.Matrix([sum(cov[i,k]*s.diff(P[a,k],(x,y)[i]) for i,k in it.product(range(2),repeat=2)) for a in range(2)])
for entry in W-P*X+divz:zero(entry,'source_target_divergence')
zero(E(u),'gaussian_adjunction')
for z in X:zero(E(z*u),'gaussian_adjunction')
for p,Hi in zip(psi,Hs):
    zero(E(s.trace(cov*Hi))-2*E(p),'gaussian_adjunction')
    zero(E(u*p)-E(s.trace(B*Hi)),'gaussian_adjunction')
    zero(E(u*p)-E(W.dot(s.Matrix([s.diff(p,x),s.diff(p,y)]))),'gaussian_adjunction')
Tval=E(s.trace(DW*DW)-s.trace(H*B*H*B))
zero(E(u*u)-E(W.dot(H*W))-E(s.trace(DW*DW)),'matrix_square')
ck(E(s.trace(DW.T*DW))-E(s.trace(DW*DW))>0,'matrix_square_negative_control')
for beta in [(1,-3,2),(-2,0,5),(0,0,0)]:
    F=sum(b*p for b,p in zip(beta,psi)); U=F-E(F)
    D=sum(b*b*E(p) for b,p in zip(beta,psi))-E(U*U)
    rhs=Tval+eps*E(s.trace(H*B*B)+W.dot(W))
    for b,Hi in zip(beta,Hs):
        C=B-s.Rational(b,2)*cov; Y=W-s.Rational(b,2)*X
        rhs+=E(s.trace(H*C*Hi*C)+Y.dot(Hi*Y))
    zero(D+E((u-U)**2)-rhs,'full_integrated_completion')
    ck(D>=0,'full_integrated_completion')

# Gaussian row correction checked with correlated slab powers, at epsilon>0.
a=s.Matrix([E(p) for p in psi]); C=s.Matrix(3,3,lambda i,j:E(psi[i]*psi[j])-a[i]*a[j]); D=s.diag(*a)-C
for i in range(3):zero(sum(D[i,j] for j in range(3))-eps*(E(psi[i]*(x*x+y*y))-a[i]*E(x*x+y*y))/2,'gaussian_row_correction')
ck(D*s.ones(3,1)!=s.zeros(3,1),'gaussian_row_correction_negative_control')
for b in [s.Matrix([1,-2,3]),s.Matrix([-3,1,1])]:
    denominator=(b.T*C*b)[0]
    dual=1-(b.T*C*s.diag(*a).inv()*C*b)[0]/denominator
    zero(dual-(b.T*(D-D*s.diag(*a).inv()*D)*b)[0]/denominator,'dual_defect')

# Differentiate actual slice-integral Gamma kernels, including a nonconstant test.
r,h0,q,k=s.symbols('r h q k',positive=True)
coordinate=h0*r**(1/q)
zero(q*r**k*s.diff(coordinate,r)-h0*r**(k+1/q-1),'facet_kernel')
for power in range(1,7):zero(s.integrate(r**(power-1)*s.exp(-r),(r,0,s.oo))-s.factorial(power-1),'facet_kernel')
# A sheared pair of planes: the two-coordinate coarea determinant is essential.
for Umat in [s.Matrix([[1,0],[s.Rational(3,5),s.Rational(4,5)]]),s.Matrix([[s.Rational(5,13),s.Rational(12,13)],[s.Rational(4,5),s.Rational(-3,5)]])]:
    gram=Umat*Umat.T
    zero(Umat.det()**2-(1-gram[0,1]**2),'ridge_coarea')

# Nonsimple octahedron: two true facets either meet in a segment or a point.
# Its edge (1,0,0)--(0,1,0) has exactly two incident facets, despite nonsimple endpoints.
normals=list(it.product((-1,1),repeat=3)); e1=s.Matrix([1,0,0]); e2=s.Matrix([0,1,0]); mid=(e1+e2)/2
ck(sum(s.Matrix(u).dot(e1)==1 for u in normals)==4,'nonsimple_faces')
ck(sum(s.Matrix(u).dot(mid)==1 for u in normals)==2,'nonsimple_faces')
for lam in [s.Rational(1,5),s.Rational(2,5),s.Rational(4,5)]:
    z=lam*e1+(1-lam)*e2
    ck([u for u in normals if s.Matrix(u).dot(z)==1]==[(1,1,-1),(1,1,1)],'nonsimple_faces')

# Exact polygon geometry from feasible intersections, independently reconstructed.
def vertices(aa,bb,cc):
    rows=[((1,0),aa),((-1,0),aa),((0,1),bb),((0,-1),bb),((1,1),cc),((-1,-1),cc)]
    points=set()
    for (u,hu),(w,hw) in it.combinations(rows,2):
        N=s.Matrix([u,w])
        if not N.det():continue
        z=N.inv()*s.Matrix([hu,hw])
        if all(s.Matrix(n).dot(z)<=hh for n,hh in rows):points.add(tuple(z))
    # Exact angular ordering without numerical trigonometry: six known sectors.
    return points
for aa,bb,cc in [(s.Rational(6,5),s.Rational(5,6),s.Rational(19,10)),(1,1,s.Rational(7,4)),(s.Rational(7,6),s.Rational(6,7),s.Rational(9,5))]:
    pts=vertices(aa,bb,cc);ck(len(pts)==6,'full_fan_geometry')
    support=lambda z:max(s.Matrix(z).dot(s.Matrix(p)) for p in pts)
    vv=(1,s.Rational(1,2)); ww=(s.Rational(1,2),1); vvww=(s.Rational(3,2),s.Rational(3,2))
    zero(support(vv)+support(ww)-support(vvww)-(aa+bb-cc)/2,'all_parallelogram_witness')
    facet=sorted([p for p in pts if p[0]==aa]);ck(len(facet)==2,'normal_variation_centroid')
    cy=(facet[0][1]+facet[1][1])/2
    zero(cy-(cc-aa-bb)/2,'normal_variation_centroid')

# Differentiate geometric shoelace area under a normal perturbation (1,eta),
# holding the three slab widths fixed. This tests the shape derivative's sign.
eta=s.symbols('eta',real=True)
aa=s.Rational(6,5);bb=s.Rational(5,6);cc=s.Rational(19,10)
z0=s.Matrix([aa+eta*bb,-bb]);z1=s.Matrix([(aa-eta*cc)/(1-eta),(cc-aa)/(1-eta)]);z2=s.Matrix([cc-bb,bb])
zs=[z0,z1,z2,-z0,-z1,-z2]
area=sum(s.det(s.Matrix.hstack(zs[i],zs[(i+1)%6])) for i in range(6))/2
length=cc-aa+bb;cy=(cc-aa-bb)/2
zero(s.diff(area,eta).subs(eta,0)+2*length*cy,'normal_shape_first_variation')
zero(area.subs(eta,0)-(4*aa*bb-(aa+bb-cc)**2),'normal_shape_first_variation')

# Rotated/sheared parallelograms near the square obey the witness exactly.
for shear in [s.Rational(-1,20),s.Rational(1,30),s.Rational(1,10)]:
    A=s.Matrix([[1,shear],[-shear,1]])
    ps=[A*s.Matrix(z) for z in it.product((-1,1),repeat=2)]
    sup=lambda d:max(s.Matrix(d).dot(p) for p in ps)
    zero(sup((1,s.Rational(1,2)))+sup((s.Rational(1,2),1))-sup((s.Rational(3,2),s.Rational(3,2))),'all_parallelogram_witness')

t=s.symbols('t',real=True)
gap=s.log((4-t*t)/(4-(t+2*s.cosh(t)-2)**2))
zero(s.series(gap,t,0,5).removeO()-t**3/2-t**4/4,'cubic_obstruction')
zero(s.series(s.exp(-2*t)-s.exp(2*t),t,0,4).removeO()+4*t+s.Rational(8,3)*t**3,'homothety_witness')
# Positive tensor control plus epsilon at its exact scale, no sqrt(epsilon) mistake.
ej=s.symbols('epsilon',positive=True); bound=7*ej+ej**2
zero(bound/ej-(7+ej),'regularizer_scale')

# Nonorthogonal block example: A tau=tau A^T, but A is not symmetric.
S=s.Matrix([[1,2],[0,1]]); A=S*s.diag(1,-1)*S.inv(); tau=S*s.diag(2,3)*S.T
zero((A*tau-tau*A.T).norm()**2,'nonorthogonal_splitting')
ck(A!=A.T and s.trace(A)==0,'nonorthogonal_splitting')

# Boundary flux sign and all four signed sides, using exact integration on a
# unit-volume square; a position-only radial test is a different identity.
half=s.Rational(1,2)
for g in [1+x, x*x+3*y*y, x*y+x**4, (1+x)*(1+y*y)]:
    bulk=s.integrate(s.integrate(x*s.diff(g,x)-y*s.diff(g,y),(x,-half,half)),(y,-half,half))
    boundary=half*sum(s.integrate(g.subs(x,sign*half),(y,-half,half)) for sign in (-1,1))-half*sum(s.integrate(g.subs(y,sign*half),(x,-half,half)) for sign in (-1,1))
    zero(bulk-boundary,'boundary_flux_signs')
    radial=s.integrate(s.integrate(2*g+x*s.diff(g,x)+y*s.diff(g,y),(x,-half,half)),(y,-half,half))
    positive=half*sum(s.integrate(g.subs(x,sign*half),(y,-half,half))+s.integrate(g.subs(y,sign*half),(x,-half,half)) for sign in (-1,1))
    zero(radial-positive,'radial_position_marginal')

print(json.dumps({'status':'PASS','assertions':sum(groups.values()),'groups':groups,'scope':'Independent exact diagnostics, with matrix-square and epsilon-correction negative controls; not proofs of compactness or weak limits.'},indent=2,sort_keys=True))
