"""Finite exact diagnostics only; no limit theorem or substantiality gate."""
from fractions import Fraction as F
from itertools import product


def mul(a,b):
    return [sum((a[j]*b[i-j] for j in range(i+1)),F(0)) for i in range(5)]


def inv(a):
    b=[1/a[0]]+[F(0)]*4
    for i in range(1,5): b[i]=-sum(a[j]*b[i-j] for j in range(1,i+1))/a[0]
    return b


def log_series(a):
    assert a[0]==1
    u=a[:];u[0]=F(0);p=[F(1)]+[F(0)]*4;out=[F(0)]*5
    for k in range(1,5):
        p=mul(p,u)
        out=[x+F((-1)**(k+1),k)*y for x,y in zip(out,p)]
    return out


def run():
    counts=dict(response_coefficients=0,one_bond_replacement=0,
                posterior_odds=0,annealed_telescoping=0,common_sheet_coefficients=0,
                physical_square_posterior=0,graph_counts=0,cutoff_failure=0)
    states=list(product((0,1),repeat=3)); signs=list(product((-1,1),repeat=3))
    factorial=[1,1,2,6,24]
    for seed in range(1,9):
        weights=[F(((j+1)*seed+j*j)%13+1) for j in range(8)]
        total=sum(weights); P=[w/total for w in weights]
        def mean(values,law=P):return sum(p*v for p,v in zip(law,values))
        def tilt(law,factors):
            ws=[p*F(factors[0])**x[0]*F(factors[1])**x[1]*F(factors[2])**x[2] for p,x in zip(law,states)]
            return [w/sum(ws) for w in ws]
        for mask in range(1,8):
            h=[F(int(sum(x[i] for i in range(3) if mask&(1<<i))%2==1)) for x in states]
            ph=mean(h);PH=[p*v/ph for p,v in zip(P,h)]
            ps=[mean([x[i] for x in states]) for i in range(3)]
            ds=[mean([x[i] for x in states],PH)-ps[i] for i in range(3)]
            ratios=[];logs=[]
            for sg in signs:
                y=[sum(a*b for a,b in zip(x,sg)) for x in states]
                den=[mean([F(v**k,factorial[k]) for v in y]) for k in range(5)]
                num=[mean([F(v**k,factorial[k]) for v in y],PH) for k in range(5)]
                ratio=mul(num,inv(den));ratios.append(ratio);logs.append(log_series(ratio))
            avg=lambda a,k:sum(v[k] for v in a)/8
            assert avg(ratios,2)==sum((1-2*p)*d for p,d in zip(ps,ds))/2
            assert avg(logs,2)==sum((1-2*p)*d-d*d for p,d in zip(ps,ds))/2
            assert sum(v[1]**2 for v in logs)/8==sum(d*d for d in ds)
            assert all(avg(a,k)==0 for a in (ratios,logs) for k in (1,3))
            counts['response_coefficients']+=5
            Y=[x[0]+x[1] for x in states];y0=mean(Y);yh=mean(Y,PH)
            vy0=mean([v*v for v in Y])-y0*y0
            vyh=mean([v*v for v in Y],PH)-yh*yh
            den=[mean([F(v**k,factorial[k]) for v in Y]) for k in range(5)]
            num=[mean([F(v**k,factorial[k]) for v in Y],PH) for k in range(5)]
            assert mul(num,inv(den))[2]==(vyh-vy0+(yh-y0)**2)/2
            counts['common_sheet_coefficients']+=1
            for r in (F(4,3),F(3,2),F(2)):
                for i in range(3):
                    factors=[F(1)]*3;factors[i]=r
                    plus=tilt(P,factors);factors[i]=1/r;minus=tilt(P,factors)
                    cosh=(r+1/r)/2;p=ps[i]
                    b=(cosh-1)*(1-2*p)/(1+2*p*(1-p)*(cosh-1))
                    cov=mean([hi*x[i] for hi,x in zip(h,states)])-ph*p
                    assert (mean(h,plus)+mean(h,minus))/2-ph==b*cov
                    counts['one_bond_replacement']+=1
                    pm=mean([x[i] for x in states],minus)
                    pha=mean(h,minus)
                    pma=mean([hi*x[i] for hi,x in zip(h,states)],minus)/pha
                    assert mean(h,plus)/pha==(1+(r*r-1)*pma)/(1+(r*r-1)*pm)
                    counts['posterior_odds']+=1
                lhs=sum(mean(h,tilt(P,[r**s for s in sg])) for sg in signs)/8-ph
                rhs=F(0)
                for i in range(3):
                    subtotal=F(0)
                    for prefix in product((-1,1),repeat=i):
                        PP=tilt(P,[r**s for s in prefix]+[F(1)]*(3-i))
                        p=mean([x[i] for x in states],PP); mh=mean(h,PP)
                        cov=mean([hi*x[i] for hi,x in zip(h,states)],PP)-mh*p
                        subtotal+=(cosh-1)*(1-2*p)*cov/(1+2*p*(1-p)*(cosh-1))
                    rhs+=subtotal/(2**i)
                assert lhs==rhs;counts['annealed_telescoping']+=1
    # Exact arithmetic in Q(sqrt(2)) for the actual n=1 wired square.
    def qa(x,y):return (x[0]+y[0],x[1]+y[1])
    def qm(x,y):return (x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    def qi(x):
        d=x[0]*x[0]-2*x[1]*x[1];return (x[0]/d,-x[1]/d)
    def qd(x,y):return qm(x,qi(y))
    def sub(x,y):return qa(x,(-y[0],-y[1]))
    def positive(x):
        a,b=x
        if a>=0 and b>=0:return a+b>0
        if a<=0 and b<=0:return False
        return a*a>2*b*b if a>0 else 2*b*b>a*a
    one=(F(1),F(0));two=(F(2),F(0))
    for r in (F(4,3),F(3,2),F(2),F(3)):
        lo=(F(0),1/r);hi=(F(0),r)
        def L(u,v):return qd(qm(u,qa(one,v)),qa(qa(two,u),qa(v,qm(u,v))))
        l=[L(u,v) for u,v in ((lo,lo),(lo,hi),(hi,lo),(hi,hi))]
        assert positive(sub(qa(l[1],l[3]),qa(l[0],l[2])))
        assert qm(l[0],l[3])!=qm(l[1],l[2])
        counts['physical_square_posterior']+=2
    for n in range(1,101):
        horizontal=[((x,y),(x+1,y)) for x in range(n) for y in range(n+1) if y!=n]
        vertical=[((x,y),(x,y+1)) for x in range(n+1) for y in range(n) if x!=0]
        assert len(horizontal)+len(vertical)==2*n*n;counts['graph_counts']+=1
    for J in range(1,10):
        assert F(1,2**J)-2<0;counts['cutoff_failure']+=1
    return dict(status='PASS',counts=counts,scope='Finite exact identities only; no universal proof, fixed-disorder asymptotic, or substantiality certification')


if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2))
