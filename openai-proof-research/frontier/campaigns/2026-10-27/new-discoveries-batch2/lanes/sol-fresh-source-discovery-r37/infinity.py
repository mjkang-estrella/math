exec(open(__file__.replace('infinity.py','probe.py')).read().split('results=[]')[0])
results=[]
for n in range(2,8):
 for a in range(n,n+6):
  for b in range(a,n+6):
   H=s.Poly(sum(c*x**i*y**j for (i,j),c in R(n,a,b).terms() if i+j==n),x,y)
   fac=s.factor_list(H.as_expr())[1]
   degs=sorted([s.Poly(q,x,y).total_degree() for q,e in fac for _ in range(e)])
   if degs!=sorted([1,n-1] if a==b and n%2 else [n]):
    results.append({'n':n,'a':a,'b':b,'H':str(s.factor(H.as_expr())),'R':str(s.factor(R(n,a,b).as_expr()))})
print(json.dumps(results,indent=2));pathlib.Path(__file__).with_name('infinity-results.json').write_text(json.dumps(results,indent=2))
