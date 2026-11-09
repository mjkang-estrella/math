"""Bounded floating diagnostics only; never an all-n proof or novelty test."""
import math,json,pathlib
import mpmath as m
m.mp.dps=100
L=pathlib.Path(__file__).resolve().parent
a=m.mpf(2)/3;theta=m.pi*a
def p(u):return 1/(1+(m.sin(theta*u)/m.sin(theta*(1-u)))**(1/a))
out={'status':'diagnostics only','mgf':[],'transport':[]}
for n in [4,16,64,256]:
 ps=[p((m.mpf(j)-m.mpf('.5'))/(2*n)) for j in range(1,2*n+1)]
 assert abs(sum(ps)-n)<m.mpf('1e-90')
 err=max(abs(sum(m.log(1-q+q*m.exp(t)) for q in ps)/n-3*m.log((1+m.exp(a*t))/2)) for t in [-8,-2,1,4,8])
 out['mgf'].append({'n':n,'max_fixed_t_error':float(err)})
for n in [1,2,4,8,16,32]:
 ps=[p((m.mpf(j)-m.mpf('.5'))/(2*n)) for j in range(1,2*n+1)]
 b=[m.mpf(1)]
 for q in ps:
  b=[b[0]*(1-q)]+[b[k]*(1-q)+b[k-1]*q for k in range(1,len(b))]+[b[-1]*q]
 x=[m.mpf(math.comb(3*n,k))/2**(3*n) for k in range(3*n+1)]
 i=j=0;u=x[0];v=b[0];d=m.mpf(0);cut=m.mpf('1e-80')
 while i<len(x) and j<len(b):
  mass=min(u,v)
  if mass>cut:d=max(d,abs(a*i-j))
  u-=mass;v-=mass
  if u<cut:
   i+=1
   if i<len(x):u=x[i]
  if v<cut:
   j+=1
   if j<len(b):v=b[j]
 out['transport'].append({'n':n,'numerical_transport_width':float(d),'width_over_n':float(d/n),'ignored_residual_threshold':'1e-80'})
assert out['mgf'][-1]['max_fixed_t_error']<out['mgf'][0]['max_fixed_t_error']
(L/'check-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
