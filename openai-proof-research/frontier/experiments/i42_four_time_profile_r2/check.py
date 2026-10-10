"""Independent exact diagnostics, read-only. Not a proof of analytic estimates."""
from fractions import Fraction as F
from itertools import product, combinations
from collections import Counter
import json, math

def check():
    counts = Counter()
    def ck(name, value):
        assert value, name
        counts[name] += 1
    def dot(x,y): return sum((a*b for a,b in zip(x,y)), F(0))
    def mv(a,x): return [dot(row,x) for row in a]
    def mm(a,b): return [[dot(row,col) for col in zip(*b)] for row in a]
    def inner(p,x,y): return sum((a*b*c for a,b,c in zip(p,x,y)),F(0))
    def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
    # Every first-failure prefix of several genuinely unequal three-leg trees.
    def tree(a,d,leg):
        here=(a,a+d,leg)
        return [here] if d==1 else tree(a,d//2,leg)+tree(a+d//2,d//2,leg)+[here]
    for lengths in [(4,8,4),(8,4,8),(8,32,8),(16,8,16),(32,4,32)]:
        nodes=[];start=0
        for j,d in enumerate(lengths): nodes+=tree(start,d,j);start+=d
        nodes.sort(key=lambda x:(x[1],x[1]-x[0]))
        ratio=F(min(lengths),max(lengths)); small=ratio/4
        for stop in range(len(nodes)):
            prefix=nodes[:stop+1]
            roots=[x for x in prefix if not any(x!=y and x[2]==y[2] and y[0]<=x[0] and x[1]<=y[1] for y in prefix)]
            roots.sort()
            ck('forest_partition', roots[0][0]==0 and roots[-1][1]==nodes[stop][1] and all(x[1]==y[0] for x,y in zip(roots,roots[1:])))
            ck('failing_root_last', roots[-1]==nodes[stop])
            ck('root_comparability',all(F(x[1]-x[0])>=ratio*(y[1]-y[0]) for i,x in enumerate(roots) for y in roots[i+1:]))
            # All singleton marks and pairs; the assertion for a set follows from its shortest mark.
            for marks in [(x,) for x in prefix]+list(combinations(prefix,2)):
                m=min(x[1]-x[0] for x in marks)
                for root in roots:
                    if root[1]-root[0]<small*m:
                        ck('small_untouched_root_after_marks',all(x[1]<=root[0] for x in marks))
    # Two-spin nonuniform Gibbs law, with exp(theta)=2, hence rational probabilities.
    states=list(product([-1,1],repeat=2)); n=len(states)
    q=[F(x*y) for x,y in states]; weight=[F(2)**int(z) for z in q]
    nu=[F(1,n)]*n; zp=dot(nu,weight); pi=[w/(n*zp) for w in weight]
    pibar=dot(pi,q); w0=[nu[i]/pi[i] for i in range(n)]
    K=[[F(0) for _ in states] for _ in states]
    Kp=[[F(0) for _ in states] for _ in states]
    rings={}
    for i,x in enumerate(states):
        opts=[]
        for site in range(2):
            ti=F(3,5)*x[1-site]
            for sign in [-1,1]:
                y=list(x);y[site]=sign;j=states.index(tuple(y))
                prob=(1+sign*ti)/4
                score=(sign-ti)*x[1-site]
                opts.append((j,prob,score));K[i][j]+=prob;Kp[i][j]+=prob*score
        rings[i]=opts
    powers=[eye(n)];derivs=[[[F(0)]*n for _ in states]]
    for k in range(6):
        powers.append(mm(powers[-1],K))
        a=mm(derivs[-1],K);b=mm(powers[-2],Kp)
        derivs.append([[a[i][j]+b[i][j] for j in range(n)] for i in range(n)])
    endweight=[1/x for x in weight]
    ep=[-q[i]*endweight[i] for i in range(n)]
    h=[mv(p,endweight) for p in powers]
    for N in [2,4,6]:
        mass=dot(nu,h[N]); massp=dot(nu,mv(derivs[N],endweight))+dot(nu,mv(powers[N],ep))
        # Enumerate every marked path, retaining self-resampling events.
        paths=[(i,F(1,n),F(0),i,[]) for i in range(n)]
        for k in range(N):
            paths=[(j,p*r,score+s,initial,history+[j]) for i,p,score,initial,history in paths for j,r,s in rings[i]]
        total=F(0); scored=F(0); initialmass=[F(0)]*n;midmass=[F(0)]*n
        for last,p,score,initial,hist in paths:
            tilt=p*endweight[last];total+=tilt;scored+=tilt*(score-q[last])
            initialmass[initial]+=tilt;midmass[hist[N//2-1]]+=tilt
        ck('marked_terminal_mass',total==mass)
        ck('marked_score_derivative',scored==massp)
        D=zp*mass; Dp=zp*pibar*mass+zp*massp
        ck('normalized_log_density_score',Dp/D==pibar+scored/mass)
        ck('normalized_path_score_zero',scored/mass-massp/mass==0)
        rho=[sum(nu[i]*powers[N//2][i][j] for i in range(n)) for j in range(n)]
        ws=mv(powers[N//2],w0)
        for i in range(n):
            ck('tilted_initial_marginal',initialmass[i]/mass==nu[i]*h[N][i]/mass)
            ck('tilted_midpoint_marginal',midmass[i]/mass==pi[i]*ws[i]**2/D)
        for k in range(N):
            for i in range(n):
                ck('doob_transition_normalization',sum(K[i][j]*h[N-k-1][j]/h[N-k][i] for j in range(n))==1)
    # Exact continuous-time Taylor coefficients, no numerical matrix exponential.
    L=[[2*(K[i][j]-F(i==j)) for j in range(n)] for i in range(n)]
    lp=[eye(n)]
    for k in range(8):lp.append(mm(lp[-1],L))
    vectors=[mv(x,w0) for x in lp]
    for k in range(9):
        lhs=sum(inner(pi,vectors[j],vectors[k-j])/math.factorial(j)/math.factorial(k-j) for j in range(k+1))
        rhs=F(2**k,math.factorial(k))*inner(pi,w0,vectors[k])
        ck('continuous_density_taylor',lhs==rhs)
    # Node recursion with a positive endpoint cap, checked exactly under a finite perturbation.
    # Cap need not satisfy analytic source estimates: only algebra is tested here.
    def kernels(weights):
        z=sum(weights);p=[w/z for w in weights];kk=[[F(0)]*n for _ in states]
        for i,x in enumerate(states):
            for site in range(2):
                for sign in [-1,1]:
                    y=list(x);y[site]=sign;j=states.index(tuple(y));opp=list(y);opp[site]*=-1;o=states.index(tuple(opp))
                    kk[i][j]+=weights[j]/(weights[j]+weights[o])/2
        pre=[[kk[i][j]/p[j] for j in range(n)] for i in range(n)]
        cap=[[1/(1+pre[i][j]) for j in range(n)] for i in range(n)]
        post=[[pre[i][j]*cap[i][j] for j in range(n)] for i in range(n)]
        par=[[sum(p[z]*post[i][z]*post[z][j] for z in range(n)) for j in range(n)] for i in range(n)]
        return p,kk,pre,cap,par
    pb,kb,preb,wb,parb=kernels(weight)
    v=F(3,2);u=(v*v-1)/(v*v+1)
    pp,kp,prep,wp,parp=kernels([w*v**int(z) for w,z in zip(weight,q)])
    for i in range(n):
        ck('perturbed_gibbs_normalization',pp[i]/pb[i]==(1+u*q[i])/(1+u*pibar))
        for j in range(n):
            bridge=[pb[z]*(preb[i][z]*wb[i][z])*(preb[z][j]*wb[z][j])/parb[i][j] for z in range(n)]
            ck('conditional_midpoint_probability',sum(bridge)==1)
            expect=sum(bridge[z]*(kp[i][z]*kp[z][j])/(kb[i][z]*kb[z][j])*(wp[i][z]*wp[z][j])/(wb[i][z]*wb[z][j]) for z in range(n) if bridge[z])
            ck('pre_ratio_gibbs_denominator',parp[i][j]/parb[i][j]==(1+u*pibar)*expect/(1+u*q[j]))
    # Exact exponent audits for all low-order allocations and replacement orders.
    eps=F(1,10000)
    ck('unmarked_four_margin',3*eps/4>F(1,10**7))
    ck('unmarked_31_margin',eps/4>F(1,10**7))
    ck('marked_regular_31_large',F(1,1000)-eps/2==F(19,20000))
    ck('marked_regular_31_small',(F(5,1000)-eps)/2==F(49,20000))
    ck('small_root_scaling',F(1,2)+F(1,4)==F(3,4))
    for k in range(5,24):
        ck('replacement_exponents',2-F(k,2)+F(k-4,3)==-F(k-4,6))
    ck('remainder24',2-F(24,6)==-2)
    ck('mesh',F(7,3)-4==F(-5,3))
    return {'status':'PASS independent exact diagnostics only','groups':dict(counts),'exact_assertions':sum(counts.values()),'floating_diagnostics':False,'limits':'Finite forest/algebra and Taylor-coefficient checks do not certify analytic source estimates, R, or W.'}

if __name__=='__main__':print(json.dumps(check(),indent=2))
