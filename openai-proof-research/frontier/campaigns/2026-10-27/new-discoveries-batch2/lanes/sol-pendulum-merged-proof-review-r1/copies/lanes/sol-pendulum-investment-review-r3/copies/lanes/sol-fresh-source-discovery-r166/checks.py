from pathlib import Path
import json,math,mpmath as m
m.mp.dps=55
L=Path(__file__).resolve().parent
rows=[]
for aa,zz in [('0.1','0.2'),('0.4','1.2'),('1.5','0.3'),('1','1'),('1.8','1.7'),('0.02','0.03')]:
 a,z=m.mpf(aa),m.mpf(zz);s=a+z
 phi=m.acos(1-a)/2;b=m.acos(1-z)/2
 T=m.quad(lambda x:1/m.sqrt(z+a-1+m.cos(2*x)),[0,phi])+m.quad(lambda x:1/m.sqrt(z+a-1+m.cos(2*x)),[0,b])
 moment=lambda n:m.quad(lambda u:2*u**(2*n)/m.sqrt(s-u*u),[0,m.sqrt(a)])+m.quad(lambda u:2*u**(2*n)/m.sqrt(s-u*u),[0,m.sqrt(z)])
 M=m.pi;partial=M;N=100
 max_rec=m.mpf(0)
 for n in range(1,N+1):
  M=m.mpf(2*n-1)/(2*n)*s*M-m.sqrt(a*z)*(a**(n-1)+z**(n-1))/n
  partial+=m.mpf(math.comb(2*n,n))/8**n*M
  if n<=5:max_rec=max(max_rec,abs(M-moment(n)))
 partial/=2*m.sqrt(2);q=max(a,z)/2
 bound=m.pi/(2*m.sqrt(2))*q**(N+1)/(1-q)
 err=abs(T-partial)
 assert err<bound+m.mpf('1e-45')
 assert max_rec<m.mpf('1e-45')
 assert abs(moment(0)-m.pi)<m.mpf('1e-45')
 assert abs(moment(1)-(m.pi*s/2-2*m.sqrt(a*z)))<m.mpf('1e-45')
 # Derivative identity for the convex convolution, n>=2.
 for n in range(2,6):
  p=m.mpf(n)-m.mpf('.5')
  B=lambda w:m.quad(lambda y:(w-y)**p/m.sqrt(a+y),[0,w])
  d=m.diff(B,z,2)
  expected=p*(p-1)*m.quad(lambda t:t**(p-2)/m.sqrt(s-t),[0,z])
  assert abs(d-expected)<m.mpf('1e-25')
 rows.append(dict(a=aa,z=zz,series_error=str(err),tail_bound=str(bound),recurrence_error=str(max_rec)))
j=json.loads((L/'curvature.json').read_text())
for r in j:
 a,z=m.mpf(r['a']),m.mpf(r['z']);assert m.mpf(r['curvature'])>=m.sqrt(a)/(16*m.sqrt(2)*z**m.mpf('1.5'))
out=dict(status='PASS',series_cases=rows,curvature_controls=len(j),convex_convolution_derivative_controls=24,scope='Finite high-precision diagnostics only. Universal proof is PROOF.md; no numerical inference of convexity.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
