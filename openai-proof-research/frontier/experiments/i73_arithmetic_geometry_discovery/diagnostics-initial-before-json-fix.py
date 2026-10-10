"""Exact finite interface diagnostics. No elliptic rank or universal proof oracle."""
from fractions import Fraction as F
from collections import Counter
from math import prod, isqrt

def legendre(a,p):
    b=pow(a%p,(p-1)//2,p)
    return 0 if b==0 else 1 if b==1 else -1

def factor(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def jacobi(a,m):
    return prod(legendre(a,p)**e for p,e in factor(m).items())

def moments(m,M=8,sieved=()):
    ans=F(1)
    for p,e in factor(m).items():
        assert p!=2
        if M%p==0:continue
        z=1+legendre(-1,p)
        ans*=F(-p,p*p-z) if p in sieved and e%2 else F(p*(p-z),p*p-z) if p in sieved else F(-1,p) if e%2 else F(p-z,p)
    return ans

def run():
    result={}
    local=[]
    for M,p in [(8,3),(8,5),(8,7),(8,13),(24,3)]:
        counts=Counter(legendre(M*M*n*n+1,p) for n in range(p))
        z=0 if M%p==0 else 1+legendre(-1,p)
        expected={0:0,1:p,-1:0} if M%p==0 else {0:z,1:(p-z-1)//2,-1:(p-z+1)//2}
        assert all(counts[k]==v for k,v in expected.items())
        allowed=[n for n in range(p*p) if (M*M*n*n+1)%(p*p)]
        conditional=Counter(legendre(M*M*n*n+1,p) for n in allowed)
        assert len(allowed)==p*p-z
        if M%p:
            assert sum(k*v for k,v in conditional.items())==-p
            assert conditional[0]==z*(p-1)
        for e in [1,2,3,4]:
            assert F(sum(legendre(M*M*n*n+1,p)**e for n in allowed),len(allowed))==moments(p**e,M,(p,))
        local.append({'M':M,'p':p,'counts_mod_p':dict(counts),'allowed_mod_p2':len(allowed),'conditioned_counts':dict(conditional)})
    result['local_polynomial_law']=local
    # Independent full enumeration of a joint period, against product formula.
    M=8;Q=3**2*5**2;allowed=[n for n in range(Q) if all((M*M*n*n+1)%(p*p) for p in [3,5])]
    assert len(allowed)==(9-0)*(25-2)
    joint=Counter((legendre(M*M*n*n+1,3),legendre(M*M*n*n+1,5)) for n in allowed)
    for a in [-1,0,1]:
        for b in [-1,0,1]:
            c3=sum(legendre(M*M*n*n+1,3)==a for n in range(9))
            c5=sum(legendre(M*M*n*n+1,5)==b for n in range(25) if (M*M*n*n+1)%25)
            assert joint[a,b]==c3*c5
    result['joint_CRT']={'period':Q,'allowed':len(allowed),'counts':{str(k):v for k,v in joint.items()}}
    # Full Gram mean is independently enumerated; short comparison checked off-period.
    coeff={1:F(1),3:F(-2,3),5:F(3,5),9:F(-1,2),15:F(2,7)}
    model=sum(a*b*moments(m*l) for m,a in coeff.items() for l,b in coeff.items())
    direct=F(sum(sum(a*jacobi(M*M*n*n+1,m) for m,a in coeff.items())**2 for n in range(15)),15)
    assert model==direct
    discrepancies=[]
    for X in [1,7,29,101]:
        empirical=sum(sum(a*jacobi(M*M*n*n+1,m) for m,a in coeff.items())**2 for n in range(1,X+1))/X
        bound=F(2,X)*sum(m*abs(a) for m,a in coeff.items())**2
        assert abs(empirical-model)<=bound
        discrepancies.append({'X':X,'error':str(abs(empirical-model)),'bound':str(bound)})
    result['Gram_comparison']={'model':str(model),'checks':discrepancies}
    # The ordinary complete-integer law incorrectly predicts zero for this first moment.
    assert moments(3)==F(-1,3) and moments(5)==F(-1,5)
    result['ordinary_model_refuted']={'p3_first_moment':str(moments(3)),'ordinary_integer_first_moment':'0'}
    # A sparse set may contain every exceptional event while preserving marginal density.
    sparse={64*n*n+1 for n in range(1,101)}
    for Y in [65,1001,10001,640001]:
        count=sum(d<=Y for d in sparse)
        assert count<=isqrt(max(Y-1,0))//8
    result['sparse_pullback']={'largest_cutoff':640001,'exception_count':100,'rank_excess_per_selected_point':2,'meaning':'logical countermodel, not elliptic ranks'}
    # Generic conic parameter and its twisting involution, exact rationals.
    for u in [F(1),F(2),F(-3),F(5,7)]:
        t=(u-1/u)/16;v=(u+1/u)/2
        assert v*v==64*t*t+1
        u2=-1/u
        assert (u2-1/u2)/16==t and (u2+1/u2)/2==-v
    result['generic_conic']='PASS rational parametrization and involution'
    # Finite symplectic two-primary summands can survive any supplied finite level.
    ranks=[sum(e>=k for e in [2,2,5,5])+1 for k in range(1,7)]
    assert ranks==[5,5,3,3,3,1]
    result['Selmer_tower_model']={'divisible_corank':1,'finite_exponents':[2,2,5,5],'level_ranks':ranks,'meaning':'abstract module only'}
    # Exact layer-cake check, independent of any asymptotic estimate.
    vals=[0,1,1,2,3,7,12];R=2;K=7;B=max(vals)
    T=lambda k:sum(a>k for a in vals)
    mass=sum(a for a in vals if a>R)
    upper=R*T(R)+sum(T(k) for k in range(R,K))+B*T(K)
    assert mass<=upper
    assert 1-2*F(3,5)==F(-1,5)
    assert min(5-6*x for x in [F(1,10),F(1,4),F(1,2)])==2
    result['tail_and_length_budget']={'mass':mass,'layer_cake_upper':upper,'terminal_log_exponent':'-1/5','comparison_error_exponent_at_Delta_half':'2'}
    return {'status':'PASS_FINITE_INTERFACES_ONLY','diagnostics':result}

if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
