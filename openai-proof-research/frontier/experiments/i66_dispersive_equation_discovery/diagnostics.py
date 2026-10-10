"""Independent finite diagnostics, not a PDE proof. No writes; JSON goes to stdout."""
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
import json, math

def compute():
    assertions=0
    def check(test):
        nonlocal assertions
        assert test
        assertions+=1
    # The source energy requirement and the differentiability requirement must overlap.
    admissible=[]
    for p in range(201,1202,2):
        a=F(1,p-1); k=(3*p+3)//4
        check(k>8)
        check(k>7-2*a+F(17,25)*p)
        check(k+3<p)
        if p in (201,401,801,1201):admissible.append([p,k,str(k-(7-2*a+F(17,25)*p)),p-k-3])
    # Independently expand the amplitude normalization to second order.
    normalizations=[]
    for p in (11,27,201,401):
        a=F(1,p-1); exponent=F(p-1)
        for kap in (F(-1,4),F(-1,17),F(0),F(1,19),F(1,4)):
            c1=-kap/2
            c2=kap*kap*(a+1)/(8*a)
            power1=exponent*c1
            power2=exponent*c2+exponent*(exponent-1)*c1*c1/2
            check(power1==-kap/(2*a))
            check(power2==kap*kap/(4*a*a))
            # A Q = -(p-1)iN; A(-kap Q/2) cancels -i kap N/(2a).
            check(-(p-1)*c1-kap/(2*a)==0)
            for logq in (F(-7),F(-1),F(0),F(2),F(5)):
                bracket2=power2+power1*kap/(2*a)-kap*logq/(4*a*a)
                check(bracket2==-kap*logq/(4*a*a))
            normalizations.append([p,str(kap),str(c1),str(c2)])
    # Rational finite sums bracket their infinite sums using integral tails.
    sums=[]
    for S in (16,64,256):
        for M in (1,4,8):
            for n in (0,1,7,31):
                x=S+n*M; count=256
                partial=sum((F(1,(x+j*M)**2) for j in range(count)),F(0))
                low=partial+F(1,M*(x+count*M))
                high=partial+F(1,M*(x+(count-1)*M))
                check(low<=high)
                check(x*high<=F(1,M)+F(1,x))
                rho=F(1,4)
                geometric=sum((rho**j*F(x*x,(x+j*M)**2) for j in range(count)),F(0))
                check(geometric<=1/(1-rho))
                check(F((x+M)**2,x*x)<=F(9,4))
                if M==4 and n==0:sums.append({'S':S,'M':M,'neutral_lower':str(x*low),'neutral_upper':str(x*high),'theory_upper':str(F(1,M)+F(1,x))})
    # A sharp telescoping forcing distinguishes the two polynomial weights exactly.
    losses=[]
    for n in (2,8,32,128,512):
        N=1024
        partial=sum((F(1,j*(j+1)) for j in range(n,N+1)),F(0))
        check(partial==F(1,n)-F(1,N+1))
        check(n*n*(partial+F(1,N+1))==n)
        losses.append({'n':n,'neutral_sigma_weight':1,'wrong_sigma_squared_weight':n})
    # Method counterexample: qualitative defects 1/(m+1) on dyadic block m.
    block_lower=[]
    for m in range(1,13):
        lo=2**m;hi=2**(m+1)
        block=sum((F(1,(m+1)*j) for j in range(lo,hi)),F(0))
        check(block>=F(1,2*(m+1)))
        block_lower.append(str(F(1,2*(m+1))))

    # Decimal Taylor jets evaluate derivatives without finite differencing.
    # Each jet coefficient is derivative/order!, and this is a finite check only.
    with localcontext() as ctx:
        ctx.prec=85
        order=6
        zero=[D(0)]*(order+1)
        def const(x):return [D(x)]+[D(0)]*order
        def add(x,y):return [a+b for a,b in zip(x,y)]
        def scale(x,c):return [a*c for a in x]
        def mul(x,y):return [sum((x[j]*y[i-j] for j in range(i+1)),D(0)) for i in range(order+1)]
        def inv(x):
            z=[1/x[0]]
            for n in range(1,order+1):z.append(-sum((x[j]*z[n-j] for j in range(1,n+1)),D(0))/x[0])
            return z
        def log(x):
            d=[D(i+1)*x[i+1] for i in range(order)]+[D(0)]
            quotient=mul(d,inv(x));return [x[0].ln()]+[quotient[i-1]/D(i) for i in range(1,order+1)]
        def power(x,n):
            out=const(1)
            while n:
                if n%2:out=mul(out,x)
                x=mul(x,x);n//=2
            return out
        jets=[]
        for p in (11,27,201):
            a=1/D(p-1);kap=D(1)/8
            for sigma in (D(8)/a,D(16)/a,D(32)/a):
                c=(-(a)*(1+kap/(2*a*sigma)).ln()).exp()
                cp_over_c=kap/(2*sigma*sigma*(1+kap/(2*a*sigma)))
                for label,r in [('core',D('0.8')),('transition',(-a*sigma/2).exp()),('small',(-2*a*sigma).exp())]:
                    z=const(r);z[1]=D(1)
                    ell=log(add(const(2),scale(mul(z,z),(2*a*sigma).exp()*c*c)))
                    bracket=add(scale(inv(ell),kap),const(1))
                    bracket=add(scale(bracket,1/(1+kap/(2*a*sigma))),const(-1))
                    imag=mul(bracket,power(z,p))
                    normalized=[]
                    for m in (0,1,3,6):
                        # Suppress harmless p-dependent combinatorial growth in reporting.
                        falling=math.prod(range(p-m+1,p+1)) if m else 1
                        val=sigma*sigma*abs(imag[m])*D(math.factorial(m))/(kap*D(falling))
                        check(val.is_finite())
                        normalized.append(format(val,'.9E'))
                    check(abs(cp_over_c*sigma*sigma-kap/(2*(1+kap/(2*a*sigma))))<D('1e-75'))
                    # Direct formula and reciprocal-difference formula agree to 75 digits.
                    direct=bracket[0]
                    rearranged=kap/(1+kap/(2*a*sigma))*(1/ell[0]-1/(2*a*sigma))
                    check(abs(direct-rearranged)<D('1e-75'))
                    jets.append({'p':p,'sigma':str(sigma),'point':label,'scaled_derivative_orders':[0,1,3,6],'scaled_abs_values':normalized})
    return {'status':'PASS finite diagnostics only','exact_and_decimal_assertions':assertions,
            'admissible_orders':admissible,'normalization_coefficients':normalizations,
            'neutral_sum_brackets':sums,'wrong_weight_growth':losses,
            'qualitative_defect_dyadic_block_lower_bounds':block_lower,
            'decimal_jet_precision':85,'decimal_jet_records':jets,
            'scope':'No numerical source-profile audit, PDE integration, universal proof, or novelty certificate.'}

if __name__=='__main__':
    print(json.dumps(compute(),indent=2,sort_keys=True))
