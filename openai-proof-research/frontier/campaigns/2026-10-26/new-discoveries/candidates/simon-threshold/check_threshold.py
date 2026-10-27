from pathlib import Path
import mpmath as m,json
m.mp.dps=70
h=lambda x:m.log(-m.expm1(-x))-x/m.expm1(x)
hp=lambda x:x*m.exp(x)/m.expm1(x)**2
def calc(g,a):
 lo=m.mpf('1e-30');hi=m.mpf(1)
 f=lambda t:h(t)-h(a*t)-m.log(g)
 while f(hi)>0:hi*=2
 for _ in range(350):
  t=(lo+hi)/2
  if f(t)>0:lo=t
  else:hi=t
 t=(lo+hi)/2;s=a*t;H=hp(t)-a*hp(s)
 b=a+(m.log(g)+m.log(-m.expm1(-a*t))-m.log(-m.expm1(-t)))/t
 d=1/(-m.expm1(-s));dd=-m.exp(-s)/(-m.expm1(-s))**2*t*hp(t)/H
 return b,d,dd,t
rows=[]
for gs in ['1.01','1.1','2','5','20']:
 g=m.mpf(gs)
 for u in ['.1','.3','.5','.9','.99','.999']:
  a=m.mpf(u)/g;b,d,dd,t=calc(g,a);eps=min(a,1/g-a)*m.mpf('1e-7')
  bm,dm,_,_=calc(g,a-eps);bp,dp,_,_=calc(g,a+eps)
  de=abs((bp-bm)/(2*eps)/d-1);dde=abs((dp-dm)/(2*eps)/dd-1)
  assert dd>0 and de<m.mpf('1e-10') and dde<m.mpf('1e-10'),(gs,u,str(de),str(dde),str(dd))
  G=lambda v:a+(m.log(g)+m.log(-m.expm1(-a*v))-m.log(-m.expm1(-v)))/v
  assert all(G(t*k)<b for k in [m.mpf('.25'),m.mpf('.5'),m.mpf('2'),m.mpf('4')])
  rows.append({k:str(v) for k,v in dict(gamma=g,alpha=a,beta=b,slope=d,curvature=dd,tau=t,first_relative_error=de,second_relative_error=dde).items()})
Path('threshold-numerics.json').write_text(json.dumps({'scope':'Independent numerical evidence only, not proof','checks':len(rows),'rows':rows},indent=2)+'\n')
print('PASS',len(rows),'optimizer, positive curvature and independent finite-difference checks at70digits')
