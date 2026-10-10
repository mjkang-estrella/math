"""Independent finite stress tests. Standard library only; no file writes."""
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from math import factorial
import json

def mul(x,y,n):
    z=[x[0]*0 for _ in range(n+1)]
    for i,a in enumerate(x[:n+1]):
        for j,b in enumerate(y[:n+1-i]):z[i+j]+=a*b
    return z

def power(x,p,n):
    z=[x[0]*0+1]+[x[0]*0]*n
    while p:
        if p&1:z=mul(z,x,n)
        p//=2
        if p:x=mul(x,x,n)
    return z

def reciprocal(x,n):
    z=[1/x[0]]+[x[0]*0]*n
    for i in range(1,n+1):z[i]=-sum(x[j]*z[i-j] for j in range(1,min(i,len(x)-1)+1))/x[0]
    return z

def logjet(x,n):
    inv=reciprocal(x,n)
    deriv=[(j+1)*x[j+1] for j in range(len(x)-1)]
    prod=mul(deriv,inv,n-1)
    return [x[0].ln()]+[prod[j-1]/j for j in range(1,n+1)]

def compute():
    counts={};records={};checks=0
    def check(t):
        nonlocal checks
        assert t
        checks+=1
    start=checks
    for p in range(201,2002,2):
        a=F(1,p-1);k=(3*p+3)//4
        check(k>7-2*a+F(17,25)*p);check(k+3<p)
        check(F(3,4)*p-7-F(17,25)*p>0)
    counts['rational_regularity']=checks-start
    # Real, not holomorphic, directional derivatives of N from polynomial coefficients.
    start=checks
    for p in [5,9,201,203]:
        for x,y in [(F(2,3),F(1,5)),(F(0),F(3,7)),(F(-1,2),F(0))]:
            for hx,hy in [(x,y),(-y,x),(F(1,7),F(-2,9))]:
                q=[x*x+y*y,2*(x*hx+y*hy),hx*hx+hy*hy]
                r=power(q,(p-1)//2,3)
                nx=mul(r,[x,hx],3);ny=mul(r,[y,hy],3)
                analytic=q[0]**((p-1)//2)
                extra=(p-1)*q[0]**((p-3)//2)*(x*hx+y*hy)
                check(nx[1]==analytic*hx+extra*x)
                check(ny[1]==analytic*hy+extra*y)
                if (hx,hy)==(x,y):
                    check(nx[1]==p*nx[0]);check(ny[1]==p*ny[0])
                if (hx,hy)==(-y,x):
                    check(nx[1]==-ny[0]);check(ny[1]==nx[0])
    # Phase correction sign on a diagonal generator with a neutral row.
    for h0 in [F(-2,7),F(0),F(5,3)]:
        H=[h0,F(3,5),F(-4,9)];gam=-h0
        q2=[F(0),H[1]/F(-2),H[2]/F(1,2)]
        check([H[0]+gam,H[1]+2*q2[1],H[2]-q2[2]/2]==[0,0,0])
    counts['real_derivatives_and_phase_sign']=checks-start
    # Exact convolution: high opposite modes create the low constant output.
    start=checks
    for N in [1,2,17,1024]:
        f={N:F(1,6),-N:F(1,6)};g={}
        for i,x in f.items():
            for j,y in f.items():g[i+j]=g.get(i+j,F(0))+x*y
        check(g[0]==F(1,18));check(g[2*N]==F(1,36))
    counts['high_to_zero_frequency']=checks-start
    # Exact finite tails with analytic integral-test upper/lower enclosures.
    start=checks;tail=[]
    for S in [20,100,1000]:
        for M in [1,7,19]:
            for n in [0,1,13]:
                sig=S+n*M;N=n+128
                partial=sum((F(1,(S+j*M)**2) for j in range(n,N+1)),F(0))
                upper=partial+F(1,M*(S+N*M))
                check(sig*partial<=F(1,M)+F(1,S))
                check(upper>=F(1,M*sig))
                check(F(S+(n+1)*M,sig)**2<=F(S+M,S)**2)
                # Positive coordinate backward index n-j-1, not n-j.
                vals=[F(1,2)**(j-n+1)/((S+j*M)**2) for j in range(n,N+1)]
                check(sig**2*sum(vals)<=1)
                tail.append(str(sig*partial))
    counts['weighted_indices_and_tail_enclosures']=checks-start
    # Abstract finite graph map: exact induced row bounds, including neutral quadratic input.
    start=checks
    S=F(100);M=F(7);K=F(100);delta=F(1,1000);eps=F(1,100000)
    for n in range(64):
        sig=S+n*M;ratio=(sig+M)**2/sig**2
        forward=ratio*(F(1,8)+1/K+delta)
        positive=K*(eps+delta) # geometric sum <=1
        neutral=K*(eps+delta)*(1/M+1/S)
        check(forward+positive+neutral<F(1,2))
    counts['finite_graph_lipschitz_budget']=checks-start
    # Compatible degree radius, all interior radii, with illustrative fixed constants only.
    start=checks
    C=F(10);S=F(100000);d=F(1,1000);kap=F(1,10000000);data=F(1,10**16);rho=d/S
    for j in range(101):
        r=rho*F(j,100)
        stable=C*S*S*(r*r+kap*r/(S*S)+data)
        check(stable<F(1,100))
    err=C*(S*rho*rho+kap*rho/S+S*data+kap/S)
    check(err<rho/2)
    counts['degree_interior_budget']=checks-start
    # Decimal jet diagnostics, separated from exact checks. n=k+3=154 at p=201.
    decimal_records=[];decimal_checks=0
    with localcontext() as ctx:
        ctx.prec=180
        p=201;n=154;a=D(1)/200
        for sigma in [D(400),D(4000)]:
            for kap in [D('-0.2'),D('0.2')]:
                c=(1+kap/(2*a*sigma)).ln()*(-a);c=c.exp()
                cp=kap/(2*sigma*sigma*(1+kap/(2*a*sigma)))
                for kind in ['core','transition','tiny','zero']:
                    r={'core':D('0.6'),'transition':(-a*sigma/2).exp(),
                       'tiny':(-2*a*sigma).exp(),'zero':D(0)}[kind]
                    # Mixed direction (3/5,4/5), base on real axis; real jets include all orders.
                    x=[r,D(3)/5];y=[D(0),D(4)/5]
                    rr=[r*r,2*r*x[1],D(1)]
                    Nfac=power(rr,100,n);Nx=mul(Nfac,x,n);Ny=mul(Nfac,y,n)
                    q=(2*a*sigma).exp()*c*c
                    ell=logjet([2+q*rr[0],q*rr[1],q],n)
                    inv=reciprocal(ell,n)
                    coef=[kap/(1+kap/(2*a*sigma))*v for v in inv]
                    coef[0]-=kap/(1+kap/(2*a*sigma))/(2*a*sigma)
                    Hx=mul(coef,Ny,n);Hy=mul(coef,Nx,n)
                    for j in range(n+1):
                        Hx[j]-=cp*(x[j] if j<len(x) else 0)
                        Hy[j]=-Hy[j]-cp*(y[j] if j<len(y) else 0)
                    # Independently use c^(p-1)*(1+kap/ell)-1.
                    direct=[c**200*kap*v for v in inv];direct[0]+=c**200-1
                    scale=max(D(1),max(abs(v) for v in coef))
                    assert max(abs(u-v) for u,v in zip(coef,direct))<scale*D('1e-150')
                    decimal_checks+=1
                    selected=[]
                    for j in [0,1,2,6,151,154]:
                        val=max(abs(Hx[j]),abs(Hy[j]))*factorial(j)*sigma*sigma/abs(kap)
                        assert val.is_finite();decimal_checks+=1
                        selected.append(format(val,'.10E'))
                    if kind=='zero':
                        assert Hx[1]==-cp*x[1] and Hy[1]==-cp*y[1];decimal_checks+=1
                    decimal_records.append({'sigma':str(sigma),'kappa':str(kap),'point':kind,
                                            'orders':[0,1,2,6,151,154],'scaled_real_jet_max':selected})
        # The next nonpolynomial Taylor coefficient at order p+2 grows exponentially.
        coeff=[]
        for sigma in [D(400),D(4000)]:
            kap=D('0.2');c=((-a)*(1+kap/(2*a*sigma)).ln()).exp()
            val=kap*c**202*(2*a*sigma).exp()/(2*D(2).ln()**2)
            coeff.append(val)
        assert coeff[1]>D(10)**14*coeff[0];decimal_checks+=1
        records['order_p_plus_2_coefficient_ratio']=format(coeff[1]/coeff[0],'.10E')
    return {'status':'PASS','scope':'finite diagnostics only, no PDE or novelty certificate',
            'exact_assertions':checks,'exact_categories':counts,'decimal_assertions':decimal_checks,
            'decimal_precision':180,'normalized_complex_jets':decimal_records,'records':records}

if __name__=='__main__':print(json.dumps(compute(),indent=2,sort_keys=True))
