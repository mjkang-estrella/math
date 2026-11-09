import pathlib,itertools,sympy as sp,json,time
D=pathlib.Path(__file__).resolve().parents[1];t=time.time();out=[];x=sp.symbols('x')
for a in range(1,11):
 par=list(range(a*a))
 def root(i):
  while par[i]!=i:i=par[i]
  return i
 def union(i,j):par[root(i)]=root(j)
 for i in range(a):
  for j in range(a):
   if i+j!=a-1:union(i*a+j,j*a+i)
 rs=sorted(set(root(i) for i in range(a*a)));ix={r:k for k,r in enumerate(rs)};n=len(rs);pred=[0]*n
 for i in range(a):
  for j in range(a):
   v=ix[root(i*a+j)]
   for k,l in [(i-1,j),(i,j-1)]:
    if k>=0 and l>=0:
     u=ix[root(k*a+l)]
     if u!=v:pred[v]|=1<<u
 ideals={0};front={0}
 while front:
  new=set()
  for mask in front:
   for v in range(n):
    if not(mask>>v&1) and pred[v]&mask==pred[v]:new.add(mask|(1<<v))
  front=new-ideals;ideals|=new
 ideals=sorted(ideals);below=[[j for j,s in enumerate(ideals) if s&m==s] for m in ideals];dp=[1]*len(ideals);vals=[1]
 for c in range(1,max(16,n+2)):
  vals.append(sum(dp));dp=[sum(dp[j] for j in js) for js in below]
 # degree n order polynomial; shift c -> c-a.
 poly=sp.interpolate([(c+a,vals[c]) for c in range(n+1)],x);factor=sp.prod(x+a-1-j for j in range(2*a-1))/sp.factorial(2*a-1)*(x if a%2==0 else 1)
 quotient,rem=sp.div(poly,factor,x);fac=sp.factor(quotient);check=all(poly.subs(x,c+a)==v for c,v in enumerate(vals));even=sp.expand(quotient.subs(x,-x)-quotient)==0
 row={'a':a,'variables':n,'ideals':len(ideals),'c_max':len(vals)-1,'counts':vals,'predicted_factor_remainder':str(rem),'quotient':str(fac),'even':even,'irreducible':bool(sp.Poly(quotient,x).is_irreducible),'interpolation_extra_checks':check};out.append(row);print(json.dumps(row),flush=True)
 (D/'outputs/qspp.json').write_text(json.dumps(out,indent=2))
 if time.time()-t>75:break
