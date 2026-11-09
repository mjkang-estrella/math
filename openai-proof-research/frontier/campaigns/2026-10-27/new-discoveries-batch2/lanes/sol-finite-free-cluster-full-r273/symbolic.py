from cluster import *
u,v,w=S.symbols('u v w',positive=True)
out={}
for n in [3,4]:
 p=cluster(n,1,u);q=cluster(n,1,v);r=cluster(n,1,w)
 out[str(n)]={'pair':str(convolution(p,r,n).as_expr()),'triple':str(convolution(convolution(p,r,n),q,n).as_expr())}
# Rank-one input convolution is exactly f-u/n*f'. Characteristic polynomial
# of diag(roots(f)) + (u/n)11^T by matrix determinant lemma (all u real).
for n in range(2,7):
 f=S.Poly(S.prod(x-t for t in range(n)),x)
 assert S.expand(convolution(f,cluster(n,1,u),n).as_expr()-f.as_expr()+u*S.diff(f.as_expr(),x)/n)==0
# Equal-scale cluster pair has exact random-overlap hypergeometric mixture.
for n in range(2,8):
 for a in range(1,n):
  for b in range(1,n):
   pair=convolution(cluster(n,a,1),cluster(n,b,1),n)
   mix=sum(Q(math.comb(a,h)*math.comb(n-a,b-h),math.comb(n,b))*x**(n-a-b+h)*(x-1)**(a+b-2*h)*(x-2)**h for h in range(max(0,a+b-n),min(a,b)+1))
   assert S.expand(pair.as_expr()-mix)==0
out['checks']='rank-one derivative identity n2..6; equal-scale hypergeometric overlap n2..7 all nontrivial a,b'
(L/'symbolic-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
