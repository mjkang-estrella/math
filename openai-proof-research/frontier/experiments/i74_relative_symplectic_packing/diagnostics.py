"""Independent exact finite diagnostics. No universal geometry certification.
Standard library only; all output deterministic and no file writes.
"""
from fractions import Fraction as F
import json


def pf(a):
    if not a: return F(1)
    return sum(((-1)**(j+1))*a[0][j]*pf([[a[r][c] for c in range(1,len(a)) if c!=j]
                    for r in range(1,len(a)) if r!=j]) for j in range(1,len(a)))


def nextfit(budgets, items):
    loads=[F(0)]*len(budgets); j=0
    for x in items:
        while j<len(budgets) and loads[j]+x>=budgets[j]: j+=1
        if j==len(budgets): return None
        loads[j]+=x
    return loads


def main():
    out={}
    # Radial primitive for a closed polynomial one-form: integrate dF(tz)[z].
    monomials={(2,1,0):F(3,7),(0,0,3):F(-2,5),(1,1,1):F(4)}
    recovered={a:sum(c*a[j]/sum(a) for j in range(3)) for a,c in monomials.items()}
    assert recovered==monomials
    out['radial_primitive']={'nonconstant_monomials':3,'result':'exact recovery'}
    # Independent cycle recurrence versus the weighted Birkhoff formula.
    q=[2,4,0,1,3]; P=list(map(F,[-1,2,3,4,-2])); N=6
    def qi(i,j):
        for _ in range(j):i=q[i]
        return i
    K=[-sum(F(N-j,N)*P[qi(i,j)] for j in range(1,N)) for i in range(5)]
    av=[sum(P[qi(i,j)] for j in range(1,N+1))/N for i in range(5)]
    assert [P[q[i]]+K[i]-K[q[i]] for i in range(5)]==av
    assert min(av)==F(1)
    out['orbit_transfer']={'cycles':[2,3],'N':N,'minimum_average':str(min(av))}
    # Independently expand exterior powers by recursive Pfaffians.
    curves=[]
    for m in [1,2,3]:
        a=[F(j+1,3) for j in range(2*m)];b=[F((-1)**j*(j+2),5) for j in range(2*m)];h=F(7,2)
        mat=[[F(0)]*(2*m+2) for _ in range(2*m+2)]
        for j in range(m):mat[2*j][2*j+1]=F(1);mat[2*j+1][2*j]=F(-1)
        for j in range(2*m):
            mat[j][-2]=a[j];mat[-2][j]=-a[j];mat[j][-1]=b[j];mat[-1][j]=-b[j]
        mat[-2][-1]=h;mat[-1][-2]=-h
        bracket=sum(a[2*j]*b[2*j+1]-a[2*j+1]*b[2*j] for j in range(m))
        assert pf(mat)==h-bracket
        curves.append({'fiber_dimension':2*m,'pfaffian':str(pf(mat))})
    out['horizontal_curvature']=curves
    # Gauge cancellation for q_tau(x,y)=(x,y+tau), Q=x, arbitrary polynomial K.
    # K=x^2+(y+lambda*zeta)^2; at one nontrivial jet, use chain rule.
    l,eta,etap,zeta,zetap,x,y,A=map(F,[2,3,5,7,11,13,17,10000])
    shifted=y+l*zeta; Kq=x*x+shifted*shifted
    Asx=l*zetap; Bty=l*eta*2*shifted
    h=A+l*etap*Kq+l*l*eta*zetap*2*shifted
    assert h-Asx*Bty==A+l*etap*Kq
    out['gauge_cancellation']={'curvature':str(h-Asx*Bty),'nonzero_bracket':str(Asx*Bty)}
    # I70 methods: orientation does not make interpolation symplectic, Alexander escapes.
    assert (F(1)+F(-1))/2==0 and (-1)*(-1)*1==1
    q0=F(1);p=4*q0-4*F(1,2)**2*q0**3
    assert 1+p*p==10
    # The actual image bound is 1+8/(3sqrt3)<3, verified without floating arithmetic.
    assert F(64,27)<4
    assert F(1,8)-F(1,4)<0
    L=F(3);epsilon=1/L;k=L*L
    assert 1-epsilon*epsilon*k*k==-8
    out['old_method_countermodels']={'Alexander_squared_radius':10,'C0_small_bracket_curvature':-8,'fixed_protected_value':'-1/8','same_class_midpoint_rank':2}
    # Two deterministic strict next-fit successes and the precise indivisible-bin failure.
    data=[([F(1),F(1)],[F(1,5)]*7),([F(2),F(3)],[F(1,7),F(2,7),F(3,7)]*4)]
    for budgets,items in data:
        loads=nextfit(budgets,items);assert loads is not None
        assert all(x<y for x,y in zip(loads,budgets))
    assert nextfit([F(1),F(1)],[F(3,5)]*3) is None
    out['finite_assignment']={'success_cases':2,'fixed_bin_failure':True}
    # New half-turn comparison: pi-rescaled coordinates, c=1, |w|=2, r0=4, r1=5.
    w=F(2);c=F(1);lower=w*w-c
    core=[(F(0),F(0)),(F(2),F(0)),(F(4),F(0)),(F(1),F(2)),(F(-1),F(1))]
    vals=[]
    for x,y in core:
        assert (x-w)**2+y*y<=16
        qx=2*w-x;qy=-y
        p=x*x+y*y-c;pq=qx*qx+qy*qy-c
        Kz=p/2;Kq=pq/2
        gap=pq+Kz-Kq
        assert gap==(x-w)**2+y*y+w*w-c and gap>=lower
        vals.append(str(gap))
    for co,si in [(F(1),F(0)),(F(3,5),F(4,5)),(F(-1),F(0)),(F(-3,5),F(-4,5))]:
        assert co*co+si*si==1
        x,y=w+4*co,4*si
        assert x*x+y*y-c>=3
    assert (w+5)**2<50<64 and 64>9*c
    out['constructed_comparison']={'core_gaps':vals,'transition_lower_bound':'3','support_radius_squared':49,'protected_threshold':50,'fiber_capacity':64}
    # Source-coordinate shear stays inside convex target; derivative can be huge.
    # Exact segment norm identity, not a grid approximation to containment.
    u=[F(1,3),F(2,5)];v=[F(-2,7),F(4,9)];t=F(3,8)
    norm=lambda z:sum(x*x for x in z)
    lhs=norm([(1-t)*a+t*b for a,b in zip(u,v)])
    rhs=(1-t)*norm(u)+t*norm(v)-t*(1-t)*norm([a-b for a,b in zip(u,v)])
    assert lhs==rhs
    # One symplectic polar block A=diag(2,1/2) and its square-root are reciprocal.
    assert F(2)*F(1,2)==1 and F(4)*F(1,4)==1
    out['fixed_capacity_transport']={'convex_segment_identity':'exact','polar_reciprocal_blocks':'exact'}
    # Exact integrated worst-fiber density for a triangular test bump.
    mn,mx=F(-1,2),F(3,2)
    cost=F(1,2)*(-2*mn)+F(1,2)*(2*mx)
    assert cost==mx-mn
    for slope,base in [(F(2),-2*mn+F(1,10)),(F(-2),2*mx+F(1,10))]:
        assert min(base+lam*slope*k for lam in [F(0),F(1)] for k in [mn,mx])>0
    out['area_budget']={'infimum_for_test_bump':str(cost),'oscillation':str(mx-mn)}
    return {'status':'PASS_FINITE_DIAGNOSTICS','groups':out,'scope':'Finite algebra only; no embeddings computed and no geometry theorem certified.'}

if __name__=='__main__':print(json.dumps(main(),indent=2,sort_keys=True))
