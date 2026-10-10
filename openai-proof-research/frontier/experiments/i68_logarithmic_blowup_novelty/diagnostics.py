"""Independent finite diagnostics of the I68 reduction, not a PDE certificate."""
from fractions import Fraction as F
import math, cmath, json

def compute():
    checks=0
    def check(x):
        nonlocal checks
        assert x
        checks+=1
    # A shorter pressure estimate using actual source inner-barrier constants.
    a=F(1,1000); h=F(999,1000)
    lower_w=(6-2*a)*h*h/12
    upper=F(67,200)+11*(F(1,16)-lower_w**2/4)
    check(upper<F(17,50))
    margins=[]
    for p in range(1001,3002,2):
        k=(3*p+3)//4
        gap=F(k)-(7-F(2,p-1)+F(17*p,25))
        check(gap>0);check(k+3<p)
        margins.append(gap)
    # Polynomial convolution kernels. No approximation of the infinite tail.
    sums=[]
    for M in (4,16,32):
        for S in (128,256,1024):
            sig=[F(S+n*M) for n in range(161)]
            for n in (0,1,8,32):
                neutral=sig[n]*sum((x**-2 for x in sig[n:]),F(0))
                check(neutral<=F(1,M)+1/sig[n])
                positive=sig[n]**2*sum((F(1,2)**(j-n+1)/sig[j]**2 for j in range(n,161)),F(0))
                check(positive<=1)
                check((sig[n+1]/sig[n])**2<2)
                # Forward source contraction remains a contraction after weighting.
                check(F(1,8)*(sig[n+1]/sig[n])**2<F(1,4))
            sums.append([S,M,str(neutral),str(positive)])
    # An exactly gauge-equivariant toy step and an exact nonlinear slice.
    gauge_errors=[]
    for t in (-1.1,-.2,0,.8,2.4):
        w=.001;u=-.0003;eps=.007;f=.00001
        beta=eps*(w+u)+f
        out=(cmath.exp(1j*(t+beta))*(1+w/8+u/4+f),
             cmath.exp(1j*(t+beta))*(2*u+eps*w+f))
        sliced=tuple(z*cmath.exp(-1j*(t+beta)) for z in out)
        err=max(abs(sliced[0]-(1+w/8+u/4+f)),abs(sliced[1]-(2*u+eps*w+f)))
        check(err<1e-14);gauge_errors.append(err)
    # Nonautonomous stable/positive recurrence with slowly vanishing coordinate
    # error, quadratic remainder and integrable forcing. Finite terminal condition.
    def solve(N):
        S=128.;M=8.;kap=.001
        sig=[S+n*M for n in range(N+1)]
        eps=[.01/(1+math.log(n+2)) for n in range(N+1)]
        w=[0.]*(N+1);u=[0.]*(N+1);hist=[]
        w0=.002/S**2
        for it in range(90):
            nw=[w0]+[0.]*N;nu=[0.]*(N+1)
            for n in range(N):
                nw[n+1]=w[n]/8+u[n]/4+kap/sig[n]**2+.1*(w[n]+u[n])**2
            for n in range(N-1,-1,-1):
                nu[n]=(nu[n+1]-eps[n]*(w[n]+u[n])-kap/sig[n]**2-.1*(w[n]+u[n])**2)/2
            dist=max(sig[n]**2*(abs(nw[n]-w[n])+8*abs(nu[n]-u[n])) for n in range(N+1))
            hist.append(dist);w,u=nw,nu
            if dist<1e-14:break
        check(hist[-1]<1e-14)
        norm=max(sig[n]**2*(abs(w[n])+8*abs(u[n])) for n in range(N+1))
        check(norm<.02)
        beta=[eps[n]*(w[n]+u[n])+kap/sig[n]**2 for n in range(N)]
        tail=0.;maxtail=0.
        for n in range(N-1,-1,-1):
            tail+=abs(beta[n]);maxtail=max(maxtail,sig[n]*tail)
        check(maxtail<.002)
        residual=max(abs(w[n+1]-w[n]/8-u[n]/4-kap/sig[n]**2-.1*(w[n]+u[n])**2)+abs(u[n+1]-2*u[n]-eps[n]*(w[n]+u[n])-kap/sig[n]**2-.1*(w[n]+u[n])**2) for n in range(N))
        check(residual<1e-17)
        return {'N':N,'iterations':len(hist),'norm':norm,'phase_tail_weight':maxtail,'residual':residual,'u0':u[0]}
    toy=[solve(n) for n in (512,1024,2048)]
    check(abs(toy[-1]['u0']-toy[-2]['u0'])<1e-17)
    # Explicit graph-domain and degree budgets for illustrative constants C=cC=1.
    degree=[]
    for S in (128,512,2048):
        d=F(1,100);kap=F(1,10000);rho=d/S;data=rho*rho/100
        stable=F(S*S)*(rho*rho+kap*rho/F(S*S)+data)
        error=rho*rho+kap*rho/F(S*S)+data+kap/F(S*S)
        check(stable<F(1,1000));check(error<rho/10)
        degree.append({'S':S,'scaled_stable':str(stable),'error_over_radius':str(error/rho)})
    return {'scope':'Finite tests of pressure budget, convolution weights, nonlinear phase slicing and a toy recurrence. Not analytic proof, source validation or priority certification.',
            'checks':checks,'pressure_upper_exact':str(upper),'pressure_margin_exact':str(F(17,50)-upper),
            'minimum_k_gap':str(min(margins)),'weighted_sums':sums,'gauge_errors':gauge_errors,
            'toy_recurrence':toy,'degree_samples':degree}

if __name__=='__main__':print(json.dumps(compute(),indent=2,sort_keys=True))
