import mpmath as m,json,pathlib
m.mp.dps=45
a=m.tan(m.pi/12);A=12*a
angles=[j*m.pi/6 for j in range(12)]
def sinc(z):return m.sin(z)/z if z else m.mpf(1)
def F(r):return sum(2*a*m.cos(t)*m.sin(r*m.cos(t))*sinc(r*a*m.sin(t))/r for t in angles)
r=m.findroot(F,(3.7,3.9));Fr=m.diff(F,r)
def boundary(v):return sum(m.quad(lambda s:v(s)*m.cos(r*(m.cos(t)-s*m.sin(t))),[-a,a]) for t in angles)
rows=[]
for k in [1,2,3,4]:
 v=lambda s: a**(2*k)-s**(2*k)
 dA=12*m.quad(v,[-a,a]);dF=boundary(v);dr=-dF/Fr+r*dA/(2*A)
 rows.append(dict(k=k,delta_area=str(dA),delta_F=str(dF),normalized_zero_derivative=str(dr)))
result=dict(status='diagnostic arbitrary precision quadrature, not certified signs or full angular proof',apothem='1',root=str(r),Fprime=str(Fr),rows=rows,uniform_offset_derivative=str(-boundary(lambda s:1)/Fr+r*(24*a)/(2*A)))
pathlib.Path(__file__).with_name('boundedchecks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
