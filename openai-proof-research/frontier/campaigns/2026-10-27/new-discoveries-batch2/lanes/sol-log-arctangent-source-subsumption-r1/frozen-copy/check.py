#!/usr/bin/env python3
import os,resource,json
os.environ.update({k:"1" for k in ["OPENBLAS_NUM_THREADS","OMP_NUM_THREADS","MKL_NUM_THREADS","NUMEXPR_NUM_THREADS"]})
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,)*2)
import mpmath as m
from pathlib import Path
m.mp.dps=75
sq=m.sqrt(2)
def g(t):return m.log(sq*m.sinh(t)/m.atan(sq*t)) if t else m.mpf(0)
def gp(t):return m.coth(t)-sq/((1+2*t*t)*m.atan(sq*t)) if t else m.mpf(0)
def lc(t):return abs(t)+m.log1p(m.exp(-2*abs(t)))-m.log(2)
def gap(t,p,q):
 s=lc(q*t)/q;x=(t+s)/2;y=(t-s)/2
 A=(g(x)+g(y))/2;h=(t+g(y)-g(x))/2
 return s/2+A+lc(p*h)/p-g(t)
def derivative(t,p,q):
 s=lc(q*t)/q;sp=m.tanh(q*t);x=(t+s)/2;y=(t-s)/2
 xp=(1+sp)/2;yp=(1-sp)/2
 h=(t+g(y)-g(x))/2;hp=(1+gp(y)*yp-gp(x)*xp)/2
 return sp/2+(gp(x)*xp+gp(y)*yp)/2+m.tanh(p*h)*hp-gp(t)
def M(a,b):return (b-a)/(sq*m.atan(m.log(b/a)/sq))
def B(a,b,r):return m.exp(m.log((a**r+b**r)/2)/r)
rows=[]
for e in [-1,1]:
 p=-e*m.sqrt(17);q=(5+e*m.sqrt(17))/2
 pts=[m.power(10,-5+i*m.mpf(9)/120) for i in range(121)]
 vals=[(t,gap(t,p,q),derivative(t,p,q)) for t in pts]
 # Validate actual nested source formula and analytic derivative independently.
 errors=[]
 for t in map(m.mpf,['.01','.1','.5','1','3','10']):
  a=m.exp(-t);b=m.exp(t);c=B(a,b,q)
  direct=m.log(B(M(a,c),M(c,b),p)/M(a,b))
  errors.append(abs(gap(t,p,q)-direct))
  errors.append(abs(derivative(t,p,q)-m.diff(lambda v:gap(v,p,q),t)))
 assert max(errors)<m.mpf('1e-60')
 rows.append({'epsilon':e,'points':len(vals),'min_gap':str(min(v[1] for v in vals)),
 'min_derivative':str(min(v[2] for v in vals)), 'negative_gaps':[str(v[0]) for v in vals if v[1]<=0],
 'negative_derivatives':[str(v[0]) for v in vals if v[2]<=0], 'identity_max_error':str(max(errors)),
 'selected':[{'t':str(t),'gap':str(v),'derivative':str(d)} for t,v,d in vals[::20]]})
# Integral C(t)=atan(sqrt2*t)/(sqrt2*t)=int_0^1 1/(1+2*t*t*u*u)du.
# Exact differentiated integral ratio is checked numerically, not a proof.
integ=[]
for t in map(m.mpf,['.1','1','10']):
 C=m.quad(lambda u:1/(1+2*t*t*u*u),[0,1]);J=m.quad(lambda u:u*u/(1+2*t*t*u*u)**2,[0,1])
 rhs=m.coth(t)-1/t+4*t*J/C
 assert abs(rhs-gp(t))<m.mpf('1e-60')
 integ.append({'t':str(t),'identity_error':str(abs(rhs-gp(t)))})
out={'status':'diagnostic_only_not_proof','limits':{'address_space_bytes':512*1024**2,'cpu_seconds':40,'threads':1},'branches':rows,'integral_checks':integ}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

# Independent high precision consistency checks for the new proof bridges.
d=m.sqrt(17);alpha=(5+d)/2;beta=(5-d)/2
f=lambda t:m.log(beta*m.sinh(alpha*t)/(alpha*m.sinh(beta*t)))/d
for t in map(m.mpf,['.01','.1','.5','1','3','10']):
 A=lambda t:(m.cosh(4*t)-m.cosh(t)*m.cosh(d*t)+5/d*m.sinh(t)*m.sinh(d*t))/2
 B0=lambda t:m.sinh(t)*(m.cosh(5*t)-m.cosh(d*t))/2
 U=lambda t:m.diff(B0,t)*A(t)-B0(t)*m.diff(A,t)-A(t)**2
 E=lambda t:(1+2*t*t)*U(t)-4*t*B0(t)*A(t)
 J=lambda t:sq*B0(t)/((1+2*t*t)*A(t))
 assert abs(A(t)/B0(t)-(m.coth(t)-m.diff(f,t)))<m.mpf('1e-55')
 assert abs(m.diff(J,t)-sq/(1+2*t*t)-sq*E(t)/((1+2*t*t)**2*A(t)**2))<m.mpf('1e-55')
 assert m.diff(f,t)>gp(t)
 for p,q in [(d,beta),(-d,alpha)]:
  a=m.exp(-t);b=m.exp(t);c=m.exp((lc(q*t))/q)
  S=lambda a,b:(beta/alpha*(b**alpha-a**alpha)/(b**beta-a**beta))**(1/d)
  assert abs(B(S(a,c),S(c,b),p)/S(a,b)-1)<m.mpf('1e-60')
print('PASS diagnostic consistency of Stolarsky, A/B and J derivative identities; not proof')
