"""Offline exact finite diagnostics, stdout only; no asymptotic proof by testing."""
from fractions import Fraction as F
from math import comb,lcm,gcd,log,sqrt
import json

def interval(J):
    # Euler transform; D_j = [4^j (j!)^2/(2j+1)!] sum_{k=0}^j 1/(2k+1).
    w=h=F(1);s=F(0)
    for j in range(J):
        s+=w*h/2**(j+1)
        w*=F(2*j+2,2*j+3);h+=F(1,2*j+3)
    return s,s+F(1,2**J)

def central(N):
    H=65*N;m=[F(0)]*H;m[0]=F(2)
    for i in range(2,H,2):m[i]=m[i-2]*F(i,i+1)
    km=[F(0)]*H;km[1]=F(2)
    for i in range(2,H):km[i]=((i-1)*km[i-2]+m[i-2]+m[i-1])/i
    def c(d):return F(comb(d,d//2),2**d) if d>=0 and d%2==0 else F(0)
    u=v=F(0)
    for h in range(2*N+1):
        i=63*N-1+h
        for j0 in range(4*N+1):
            j=7*N+j0;w=(-1)**(h+j0)*comb(2*N,h)*comb(4*N,j0)
            u+=4*w*c(i-j)
            v+=w*(km[i-j]-sum((m[i-j+k-1]/k for k in range(1,j+1)),F(0)))
    assert u==4*sum(((-1)**j*comb(6*N,j)*c(52*N-1+j) for j in range(6*N+1)),F(0))
    E=lcm(u.denominator,v.denominator);A=int(E*u);B=int(E*v)
    cap=2**(H+2)*lcm(*range(1,H+1))**5
    assert cap%E==0
    return u,v,E,A,B

def cf_bounded(x,M):
    a,b=x.numerator,x.denominator;pm2,pm1,qm2,qm1=0,1,1,0
    while b:
        k=a//b;p=k*pm1+pm2;q=k*qm1+qm2
        if q>M:break
        pm2,pm1,qm2,qm1=pm1,p,qm1,q;a,b=b,a-k*b
    assert 1<=qm1<=M
    return pm1,qm1

# Compare the closed Euler terms with original finite differences, independently.
row=[F(1,(2*k+1)**2) for k in range(21)];w=h=F(1)
for j in range(20):
    assert row[0]==w*h
    row=[row[k]-row[k+1] for k in range(len(row)-1)]
    w*=F(2*j+2,2*j+3);h+=F(1,2*j+3)
cs=[central(N) for N in range(1,5)];out=[];forms=[]
for N in range(1,4):
    u,v,E,A,B=cs[N-1];u1,v1,E1,A1,B1=cs[N]
    det=A*B1-A1*B;d=abs(det);assert d>0
    M=2**N*d;J=2*M.bit_length()+5;lo,hi=interval(J)
    assert u*hi+v>0 if N%2 else u*lo+v<0
    p,q=cf_bounded((lo+hi)/2,M);Q=d*q;P=-d*p
    err=max(abs(Q*lo+P),abs(Q*hi+P));assert err<F(2,2**N)
    assert not (Q*lo+P<=0<=Q*hi+P)
    z0=F(B1*Q-A1*P,det);z1=F(-B*Q+A*P,det)
    assert z0.denominator==z1.denominator==1
    assert A*z0+A1*z1==Q and B*z0+B1*z1==P
    assert abs(Q)<=d*M and abs(P)<=2*d*M
    assert max(abs(z0),abs(z1))<=3*max(abs(A),abs(B),abs(A1),abs(B1))*M
    forms.append((Q,P))
    out.append({'N':N,'index_bits':d.bit_length(),'M_bits':M.bit_length(),'Euler_terms':J,'Q_bits':Q.bit_length(),'P_bits':abs(P).bit_length(),'combination_max_bits':max(abs(z0.numerator),abs(z1.numerator)).bit_length(),'error_bound':f'2^(1-{N})','actual_error_upper_float':float(err),'adjacent_direction_distinct':None if N==1 else forms[-1][0]*forms[-2][1]!=forms[-2][0]*forms[-1][1]})
# Rational holonomic recurrence and exact coefficient caps.
b=[F(0),F(1)];a=[F(1),F(4)];L=1
for n in range(2,41):
    a.append(-((32*(n-1)**2-4)*a[-1]+256*(n-2)**2*a[-2])/n**2)
    b.append((F(16 if n==2 else 0)-(32*(n-1)**2-4)*b[-1]-256*(n-2)**2*b[-2])/n**2)
for n in range(1,41):
    L=lcm(L,n);assert a[n].denominator==1 and (b[n]*L**2).denominator==1
# Transcribe Eskandari's rates; these rows are floating diagnostics only.
phi=(1+sqrt(5))/2;R=16*phi**5;rate=[]
for alpha in [0,1,3,3.31765,4,10]:
    li=-log(16)-log(1+alpha)+(alpha*log(alpha/(1+alpha)) if alpha else 0)
    le=-5*log(phi)+alpha*log(16*phi**-5-1);lm=max(li,le)
    u=log(R)+alpha*log(1+R)-log(16);den=log(16)+4*(1+alpha)
    rate.append({'alpha':alpha,'denominator_multiplier_rate':den,'integral_decay_rate':-lm,'cleared_form_growth':den+lm,'height_rate':den+u,'sequence_index_bound':(u-lm)/(den+u)})
print(json.dumps({'evidence':'PASS finite exact algebra; rates explicitly floating','lattice':out,'holonomic_coefficients_tested':40,'Euler_difference_terms':20,'hypergeometric_rates':rate,'universal_cleared_growth_lower_float':log(__import__('math').exp(4)-1)},sort_keys=True,indent=2))
