import mpmath as m,json,pathlib
m.mp.dps=40
P=pathlib.Path(__file__).resolve().parent
F=lambda a,b,u:m.betainc(a,b,0,u,regularized=True)
def med(a,b):
 lo=m.mpf(0); hi=m.mpf(1)
 for _ in range(145):
  v=(lo+hi)/2
  if F(a,b,v)<m.mpf('.5'):lo=v
  else:hi=v
 return (lo+hi)/2
out=[]
for aa,bb in [(1,1),(1,2),(1,10),(1.1,3),(2,2),(2,4),(2,20),(5,10),(10,20)]:
 a=m.mpf(aa);b=m.mpf(bb);n=a+b-m.mpf(2)/3;u=med(a,b)
 f=lambda x:x**(a-1)*(1-x)**(b-1)/m.beta(a,b)
 psi=m.digamma(b)-m.digamma(a+b)
 cov=m.quad(lambda x:f(x)*(m.log(1-x)-psi),[0,u])
 derivative=cov-u*f(u)/n
 fd=m.diff(lambda v:F(a,v,n*u/(a+v-m.mpf(2)/3)),b)
 assert abs(derivative-fd)<m.mpf('1e-32')
 out.append(dict(a=str(a),b=str(b),median=str(u),relative_error=str((a-m.mpf(1)/3)/(n*u)-1),scaled_cdf_derivative_at_median=str(derivative),identity_residual=str(abs(derivative-fd))))
# Exact a=b=1 formula shows no global CDF ordering shortcut.
obstruction=[]
for u in [m.mpf('.01'),m.mpf('.5')]:
 d=-(1-u)*m.log(1-u)-m.mpf(3)/4*u
 obstruction.append({'u':str(u),'scaled_cdf_derivative':str(d)})
assert m.mpf(obstruction[0]['scaled_cdf_derivative'])>0
assert m.mpf(obstruction[1]['scaled_cdf_derivative'])<0
report={'precision':40,'diagnostic_only':True,'median_cases':out,'stochastic_order_shortcut_obstruction':obstruction,'source_counterexample':False,'complete_proof':False}
(P/'checks.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
