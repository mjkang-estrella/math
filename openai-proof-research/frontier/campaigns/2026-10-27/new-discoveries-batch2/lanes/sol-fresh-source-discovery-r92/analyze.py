exec((__import__('pathlib').Path(__file__).parent/'check.py').read_text().split('out=[]')[0])
import sympy as s
x=s.symbols('x');out=[];start=time.monotonic()
for n in range(2,37):
 a,c=row(n);bad=[k for k in range(2,n-1) if a[k]**2<a[k-1]*a[k+1]]
 # b from c expansion around m=1
 diff=[0]+c[1:]+[sum(a[k]*comb(n,k) for k in range(n))];b=[];d=diff[1:]
 while d:b.append(d[0]);d=[v-u for u,v in zip(d,d[1:])]
 assert all(sum(b[k-1]*comb(m-1,k-1) for k in range(1,min(m,n)+1))==sum(a[k]*comb(m,k) for k in range(min(m,n-1)+1)) for m in range(1,n+1))
 out.append({'n':n,'a':a,'b':b,'LC_a_failures':bad,'LC_b_failures':[k for k in range(1,n-1) if b[k]**2<b[k-1]*b[k+1]],'modes':[k for k in range(1,n) if a[k]==max(a)],'realrooted_a':s.Poly(sum(a[k]*x**(k-1) for k in range(1,n)),x).count_roots(-s.oo,0)==n-2})
 print(n,out[-1]['modes'],'LC',bad,'RR',out[-1]['realrooted_a'],flush=True)
(L/'analysis-results.json').write_text(json.dumps({'rows':out,'wall':time.monotonic()-start},indent=2))
