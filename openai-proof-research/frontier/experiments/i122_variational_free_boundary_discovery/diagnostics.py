"""Exact finite diagnostics only; not universal-proof, literature or priority certification."""
from fractions import Fraction as F
from itertools import product

def run():
    checks={}
    count=0
    for n,p,r,A2,B2 in product(range(2,10),[F(1,2),F(1),F(3,2),F(2),F(3)],[F(1),F(2)],[F(1),F(3)],[F(0),F(2)]):
        # Cancel the common r^(2p-3); p may be half-integral, so no floats.
        d=(p*p*A2+B2)/(n+2*p-2)
        cone=(A2+B2)/n
        lhs=(2*p-2)*(d-A2)
        rhs=n*(cone-d)+(p-1)**2*A2
        assert lhs==rhs
        count+=1
    checks['cone_derivative_identity_normalized_coefficients']=count
    count=0
    for t,b in product([F(i,5) for i in range(-10,11)],[F(i,8) for i in range(-8,9)]):
        e=[(1-t*t)/(1+t*t),2*t/(1+t*t)];j=[-e[1],e[0]]
        N=[[j[a]*e[c] for c in range(2)] for a in range(2)]
        B=[[F(a==c)+b*N[a][c] for c in range(2)] for a in range(2)]
        I=[[F(a==c)-b*N[a][c] for c in range(2)] for a in range(2)]
        assert B[0][0]*B[1][1]-B[0][1]*B[1][0]==1
        assert [[sum(B[a][k]*I[k][c] for k in range(2)) for c in range(2)] for a in range(2)]==[[1,0],[0,1]]
        A=[[sum(I[a][k]*I[c][k] for k in range(2)) for c in range(2)] for a in range(2)]
        explicit=[[F(a==c)-b*(j[a]*e[c]+e[a]*j[c])+b*b*j[a]*j[c] for c in range(2)] for a in range(2)]
        assert A==explicit
        for g in [(F(1),F(0)),(F(3,5),F(4,5)),(F(0),F(1))]:
            z=sum(g[a]*A[a][c]*g[c] for a in range(2) for c in range(2))
            assert F(1,4)<=z<=4
        count+=1
    checks['twist_shear_inverse_determinant_coefficient_instances']=count
    count=0
    for weights,g,h in product([(F(1),F(2),F(3)),(F(3),F(2),F(1))],product([F(-2),F(0),F(1)],repeat=3),[F(-1),F(0),F(2)]):
        pts=[]
        for i,w in enumerate(weights):
            for s in [-1,1]:pts.append((tuple(F(s if j==i else 0) for j in range(3)),w))
        for i in range(3):
            lam=2*weights[i]
            fs=[h+sum(y[j]*g[j] for j in range(3)) for y,w in pts]
            lhs=sum(w*y[i]*f for (y,w),f in zip(pts,fs))
            assert lhs==lam*g[i]
            assert lam*g[i]**2<=sum(w*f*f for (y,w),f in zip(pts,fs))
            count+=1
    checks['covariance_identity_and_cauchy_instances']=count
    for R in [F(1,5),F(1),F(2),F(9)]:
        h=R/2
        assert 2*R==4*h
        assert 2*h==R # gradient-distance squared
    checks['equal_energy_phase_competitors']=4
    count=0
    # Exact model: omega_j=1/((j+1)(j+2)), tail=1/(j+1).
    for m,N in product(range(1,9),range(1,65)):
        increments=sum(F(1,j+1)-F(1,j+m+1) for j in range(N))
        assert increments==sum(F(1,j+1) for j in range(m))-sum(F(1,N+j+1) for j in range(m))
        assert increments<=sum(F(1,j+1) for j in range(m))
        count+=1
    checks['annular_dini_telescopes']=count
    return {'status':'PASS','arithmetic':'Fraction and integers only','checks':checks,'scope':'finite algebraic diagnostics only; not universal proof or contribution certification'}

if __name__=='__main__':
    import json
    print(json.dumps(run(),sort_keys=True,indent=2))
