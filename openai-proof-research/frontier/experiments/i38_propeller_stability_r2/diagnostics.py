#!/usr/bin/env python3
"""Independent rational certificates and explicitly noncertified stress tests.

No universal theorem is proved by finite testing. All rational interval endpoints
use Fraction and integer square roots. Gaussian activation quadrature is separate.
"""
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path

class I:
    def __init__(self,a,b=None):
        self.a=F(a);self.b=F(a if b is None else b);assert self.a<=self.b
    @staticmethod
    def cast(x): return x if isinstance(x,I) else I(x)
    def __add__(self,x):
        x=I.cast(x);return I(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self): return I(-self.b,-self.a)
    def __sub__(self,x): return self+-I.cast(x)
    def __rsub__(self,x): return I.cast(x)+-self
    def __mul__(self,x):
        x=I.cast(x);v=[self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=I.cast(x);assert not x.a<=0<=x.b;return self*I(1/x.b,1/x.a)
    def __rtruediv__(self,x): return I.cast(x)/self
    def __pow__(self,n):
        assert n>=0
        if n%2==0:
            return I(0 if self.a<=0<=self.b else min(self.a**n,self.b**n),max(self.a**n,self.b**n))
        return I(self.a**n,self.b**n)
    def sqrt(self):
        assert self.a>=0;D=10**65
        lo=math.isqrt((self.a*D*D).numerator//(self.a*D*D).denominator)
        hi=math.isqrt((self.b*D*D).numerator//(self.b*D*D).denominator)+1
        return I(F(lo,D),F(hi,D))
    def bounds(self): return [str(self.a),str(self.b)]

def atan_point(x,n=52):
    x=F(x);assert 0<=x<=1
    terms=[(-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n+2)]
    a=sum(terms[:n+1]);b=a+terms[n+1];return I(min(a,b),max(a,b))

PI=16*atan_point(F(1,5))-4*atan_point(F(1,239))
PHI0=1/(2*PI).sqrt()
B2=9/(8*PI)

def exp_negative(y):
    y=F(y);assert y>=0
    vals=[sum((-y)**j/F(math.factorial(j)) for j in range(n+1)) for n in [79,80]]
    return I(*vals)

def phi(x):
    x=F(x);return PHI0*exp_negative(x*x/2)

def Phi(x):
    x=F(x)
    if x<0:return 1-Phi(-x)
    vals=[sum((-1)**j*x**(2*j+1)/F(2**j*math.factorial(j)*(2*j+1)) for j in range(n+1)) for n in [79,80]]
    return I(F(1,2))+PHI0*I(*vals)

def G(x):
    p=Phi(x);f=phi(x);return f*(F(x)*p+f)/(p*p)

def arcsin_point(x):
    x=F(x);assert 0<=x<1
    n=40;q=sum(F(math.comb(2*j,j),4**j*(2*j+1))*x**(2*j+1) for j in range(n))
    return I(q,q+x**(2*n+1)/((2*n+1)*(1-x*x)))

def certificate_checks():
    checks={}
    def positive(name,x,threshold=0):
        x=I.cast(x)-F(threshold);assert x.a>0,(name,x.bounds())
        checks[name]={'status':'PASS','strict_slack_lower':str(x.a)}
    positive('pi_lower',PI,'3.14159');positive('pi_upper',I('3.14160')-PI)
    def df(x):return 2*F(x)-phi(x)/Phi(-F(x))
    positive('normal_minimum_left_sign',-df('.6119'))
    positive('normal_minimum_right_sign',df('.6121'))
    ff=F(9,4)*Phi(F('-.612'))/exp_negative(F('.612')**2)
    positive('normal_minimum_value',ff*(1-F(1,10**7)),'.8843837')
    df_interval=2*I('.6119','.6121')-I(phi('.6121').a,phi('.6119').b)/I(Phi('-.6121').a,Phi('-.6119').b)
    positive('normal_log_derivative_lower',df_interval+F(1,1000))
    positive('normal_log_derivative_upper',F(1,1000)-df_interval)
    def cap(x):
        x=F(x);p=F(1,2)-(arcsin_point(x)+x*I(1-x*x).sqrt())/PI
        f=6*x*p-2/PI*I((1-x*x)**3).sqrt()
        rr=F(9,4)*p/(1-x*x)**3
        return p,f,rr
    p0,f0,r0=cap('.29');p1,f1,r1=cap('.294')
    positive('cap_left_sign',-f0);positive('cap_right_sign',f1)
    positive('cap_H_interval',p1-F('.294')/PI)
    positive('cap_endpoint',r0,'.9312526')
    positive('cap_derivative_slack',F('.03')-F(9,4)*I(max(-f0.a,f1.b))/(1-F('.294')**2)**4)
    positive('cap_minimum',r0-F('.03')*F('.004'),'.929')
    table=[('0','.05','1'),('.05','.14','.91'),('.14','.24','.87'),('.24','.33','.836'),('.33','.41','.809'),('.41','.48','.788'),('.48','.54','.771'),('.54','.59','.756'),('.59','.64','.743'),('.64','2/3','.73')]
    qs=['-2.033','-1.548','-1.238','-1.024','-.860','-.728','-.621','-.535','-.450']
    for j,(a,b,u) in enumerate(table):
        a,b,u=map(F,[a,b,u])
        if j:
            q=F(qs[j-1]);positive(f'quantile_{j}',(F('.415')+F('.15')*a)*a-Phi(q))
            positive(f'G_upper_{j}',u-G(q))
        positive(f'probability_interval_{j}',B2/(1+I(1-a*a).sqrt())-u*(F('.415')+F('.15')*b)**2)
    q=F('.066')
    positive('third_radius',F(1,9)*(F('.415')/F('.23')-F('.734'))-F('.116'))
    positive('large_third_small_minimum',(F('.44')**2-q*q)*(F('.44')**2-2*q*q)-8*(3/PI)**2*q*q)
    for j,(a,b) in enumerate([('.23','.30'),('.30','.35'),('.35','.41'),('.41','.44')]):
        a,b=map(F,[a,b]);m=1-F('.116')/(F('.415')/b-F('.734'))-b*b-2*q*q
        positive(f'small_minimum_factor_{j}',m)
        positive(f'small_minimum_gap_{j}',(a*a-q*q)*m-8*(3/PI)**2*q*q)
    for aa,m,k in [('.929',5,2),('.884',6,3)]:
        a=F(aa);d=a-F('.15');s=F('.415')/d
        def e(x):return F('.415')*x-d*x*x
        K=d*F('.42')/(s+F('.42'))
        positive(f'tail_endpoint_{aa}',e(1/I(5).sqrt())-e(q))
        positive(f'four_radius_gap_{aa}',K*(4*s*s-1+(m-4)*q*q)+(m-4)*e(q)-(1-a))
        positive(f'cap_budget_{aa}',k*e(F('.42'))-(1-a))
        t0=(F('.415')-I(F('.415')**2-4*d*(1-a)/k).sqrt())/(2*d)
        positive(f't0_upper_{aa}',F('.12')-t0)
        positive(f'final_charge_one_{aa}',e(F('.23'))+k*e(q)-(1-a))
        positive(f'final_charge_two_{aa}',e(I(F('2.6')*q).sqrt())+k*e(q)-(1-a))
        positive(f'final_endpoint_{aa}',s*s-F('2.6')*t0)
    positive('strict_final_determinant_gap',F('1.5')*(F('2.6')-F('.12'))**2-10*(3/PI)**2)
    # Singular residual pairs and zero correlations included; exact PSD tests.
    psd=singular=0
    for a,b,c in itertools.product([F(j,16) for j in range(17)],repeat=3):
        det=1-a*a-b*b-c*c-2*a*b*c
        if det<0:continue
        assert a*a+b*b+c*c<=a+b+c<=F(3,2)
        assert (1-a*a)+(1-b*b)+(1-c*c)>=F(3,2)
        psd+=1;singular+=int(det==0)
    simplex=0
    for i in range(21):
      for j in range(21-i):
       for k in range(21-i-j):
        a,b,c=F(i,20),F(j,20),F(k,20)
        val=sum((1+x)**2*(1+y)**2 for x,y in [(a,b),(a,c),(b,c)])
        assert val<=F(88,9)<10;simplex+=1
    return {'rational_interval_certificates':checks,'psd_correlation_cases':psd,
            'singular_correlation_cases':singular,'residual_simplex_cases':simplex,
            'scope':'Strict margins and finite adversarial checks. Not a universal proof by enumeration.'}

def simpson(fn,a,b,n):
    h=(b-a)/n
    return h/3*(fn(a)+fn(b)+sum((4 if i%2 else 2)*fn(a+i*h) for i in range(1,n)))

def cone_gain(a,c):
    # Exact analytic formula [a-c atan(a/c)]/sqrt(2pi), stably evaluated.
    x=a/c
    return c*sum((-1)**(j+1)*x**(2*j+1)/(2*j+1) for j in range(1,12))/math.sqrt(2*math.pi)

def activation_checks():
    rows=[];B=3/(2*math.sqrt(2*math.pi));e0=(B/1600)**2
    for kind,n in [('single',1),('coherent',256),('antipodal',256),('only_common_mean',0)]:
      for share in ([1.] if n==0 else [0.,.25,.75]):
       for energy in [e0/2,e0/100,1e-12]:
        mu=math.sqrt(energy*share/3)
        amp=math.sqrt(energy*(1-share)/max(n,1))
        high=amp if n else 0.
        low=-amp if kind=='antipodal' else 0.
        ap=max(0.,high-mu);am=max(0.,mu-low)
        def fn(theta):
            c=math.sqrt((1-energy)/3)*math.cos(theta)
            return cone_gain(ap,c)+cone_gain(am,c)
        val=3/math.pi*simpson(fn,0,math.pi/3,400)
        ratio=val/energy**1.5
        assert 0<=ratio<400
        rows.append({'kind':kind,'tail_labels':n,'mean_energy_share':share,
                     'energy':energy,'gain_over_E_3_over_2':ratio,
                     'status':'NONCERTIFIED angular quadrature; rank-one arbitrary sign correlation'})
    # Deterministic pointwise test of (6.2), including plane projections, common
    # mean, null extra scores and activation-scale points (ordinary Monte Carlo
    # would almost never sample the tiny relevant planar radii).
    count=0;worst=0.
    for n,share in itertools.product([1,4,257],[.0,.3,.9]):
        E=e0/2;S=math.sqrt(1-E)
        mu=[math.sqrt(E*share/6),0.,math.sqrt(E*share/6)]
        tails=[]
        for j in range(n):
            ang=2*math.pi*j/max(n,1);p=math.sqrt(E*(1-share)/n)
            tails.append([p*math.cos(ang)/math.sqrt(2),p*math.sin(ang)/math.sqrt(2),p*(-1 if j%2 else 1)/math.sqrt(2)])
        head=[[S*math.cos(2*math.pi*j/3)/math.sqrt(3),S*math.sin(2*math.pi*j/3)/math.sqrt(3),0.] for j in range(3)]
        for theta,rscale,z in itertools.product([2*math.pi*j/24 for j in range(24)],[0.,.01,.1,.5,1.,5.,100.],[-8.,-1.,0.,1.,8.]):
            R=math.sqrt(E)*rscale;g=[R*math.cos(theta),R*math.sin(theta),z]
            dot=lambda v:sum(x*y for x,y in zip(v,g))
            hm=max(dot(u)+dot(mu) for u in head)
            gain=max([0.,hm]+[dot(v) for v in tails])-hm
            Z=math.sqrt(sum((v[2]*z)**2 for v in tails))+abs(mu[2]*z)
            rhs=max(0.,Z-R/(8*math.sqrt(3)))
            excess=gain-rhs;worst=max(worst,excess)
            assert excess<2e-15;count+=1
    return {'rank_one_activation':rows,'pointwise_projection_cases':count,
            'max_pointwise_excess':worst,'scope':'NONCERTIFIED floating stress checks; analytic proof is in review.'}

def run():return {'exact':certificate_checks(),'noncertified':activation_checks()}

if __name__=='__main__':
    result=run()
    print(json.dumps(result,indent=2))
