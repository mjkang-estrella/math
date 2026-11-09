from fractions import Fraction as F
import json

def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out

def witness(a,b):
    norm=a*a+b*b
    slope=(3*a*a-b*b)/6
    intercept=-a*(a*a+b*b)/3
    # Independently compare coefficients of f(z)*(z+2a)/6 and g-Lg.
    product=mul([norm,-2*a,F(1)],[a/3,F(1,6)])
    assert product==[-intercept,-slope,F(0),F(1,6)]
    assert b>0 and norm<1
    err=abs(F(1,2)-slope); baseline=abs(1-a)
    c=1-a; e1=2*c; e2=c*c+b*b; h2=e1*e1-e2
    Q=1-h2/(3*e1)
    assert err/baseline==Q
    return dict(norm_squared=str(norm),slope=str(slope),intercept=str(intercept),
                error_at_one=str(err),baseline_at_one=str(baseline),
                gap=str(err-baseline),shifted_h2=str(h2),source_Q=str(Q))

def run():
    main=witness(F(3,4),F(1,2))
    assert main['error_at_one']=='25/96' and main['gap']=='1/96'
    zero=witness(F(1,100),F(1,2))
    a=F(1,100); b=F(1,2)
    zero_error=abs((3*a*a-b*b)/6)
    assert zero_error==F(2497,60000)>a
    # Parametric bridge is proved symbolically in review.md; these checks
    # independently test representative rational members, not prove universality.
    for c in [F(1,10),F(1,4),F(1,3)]:
        b2=c; h2=3*c*c-b2
        assert (1-c)**2+b2<1
        assert (h2<0)==(c<F(1,3))
    assert max(abs(F(-23,96)),abs(F(25,96)))==F(25,96)<F(7,4)
    return {'status':'PASS','main':main,'zero_error':str(zero_error),
            'zero_baseline':str(a),'uniform_witness_error':'25/96',
            'uniform_conjecture_rhs':'7/4','uses_candidate_checker':False}

if __name__=='__main__':print(json.dumps(run(),indent=2))
