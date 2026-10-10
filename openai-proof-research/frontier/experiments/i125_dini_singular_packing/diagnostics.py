"""Finite exact algebra checks only; no universal-proof/contribution certification."""
from fractions import Fraction as Q

def run():
    counts={}
    c=0
    for n in range(8,17):
        for D in range(1,33):
            b=Q(1,2**(n+4)*(D+1)); a=b**n
            assert D*b*b<=Q(1,2**n)
            for j in range(12):
                f=a*Q(1,2**(n*j))
                # f^(2/n)=b^2*2^(-2j), with no floating roots.
                assert D*4**j*f*b*b*Q(1,2**(2*j))<=a*Q(1,2**(n*(j+1)))
                c+=1
    counts['clearing_iteration_invariant']=c
    c=0
    for aa in [Q(1,2),Q(1),Q(2)]:
        for bb in [Q(1,3),Q(1),Q(3)]:
            for px in range(-2,3):
                for py in range(-2,3):
                    for gx,gy in [(0,0),(1,0),(0,1),(2,-1),(-2,3)]:
                        q2=Q(3,2)
                        d=q2-Q(px*px)/aa-Q(py*py)/bb
                        ep=aa*(Q(gx)-Q(px)/aa)**2+bb*(Q(gy)-Q(py)/bb)**2
                        assert aa*gx*gx+bb*gy*gy+q2==ep+d+2*(px*gx+py*gy)
                        c+=1
    counts['fixed_flux_square_completion_positive_phase']=c
    c=0
    for m in range(1,9):
        weights=[Q(1,(j+1)*(j+2)) for j in range(128)]
        for start in range(16):
            total=sum(sum(weights[j:j+m]) for j in range(start,100))
            assert total<=m*sum(weights[start:100+m-1])
            c+=1
    counts['annular_overlap_positive_increments']=c
    c=0
    for omega in [Q(j,31) for j in range(32)]:
        for eps in [Q(j,17) for j in range(18)]:
            for tau in [Q(1,8),Q(1,2),Q(2)]:
                assert omega*eps<=tau*eps*eps+omega*omega/(4*tau)
                c+=1
    counts['phase_mismatch_young_absorption']=c
    c=0
    theta=Q(1,2)
    for N in range(1,65):
        forcing=[Q(1,(j+1)**2) for j in range(N)]
        e=Q(1); total=e
        for g in forcing:
            e=theta*e+g; total+=e
        assert total<=(Q(1)+sum(forcing))/(1-theta)
        c+=1
    counts['flatness_recurrence_sum_bound']=c
    return {'status':'PASS','arithmetic':'Fraction and integers only','checks':counts,
            'scope':'finite algebraic diagnostics only; not universal proof or substantiality certification'}

if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
