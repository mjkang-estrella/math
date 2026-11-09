from cluster import *
def run3():
 total=0;near=0
 for n in [3,4,5]:
  templates=[]
  for a in range(1,n-1):
   for b in range(1,n-a):
    c=n-a-b
    for v in [Q(1,100),Q(1,2),Q(99,100)]:
     templates.append(S.Poly(x**a*(x-v)**b*(x-1)**c,x))
  # Compact deterministic test: p=q or a reflected q; all r templates.
  for p,r in itertools.product(templates,repeat=2):
   for q in [p,S.Poly((-1)**n*p.as_expr().subs(x,-x),x)]:
    pr=convolution(p,r,n);qr=convolution(q,r,n);t=convolution(pr,q,n)
    T,A,B,C=map(roots,[t,pr,qr,r]);total+=1
    for j in range(1,n+1):
     for k in range(1,n+2-j):
      i=j+k-1
      for branch,l in [('max',max(j,k)),('reflected',n+1-max(j,k))]:
       gap=T[i-1][0]+C[l-1][0]-A[j-1][1]-B[k-1][1]
       if gap>0:
        o=dict(n=n,branch=branch,indices=[i,l,j,k],coeffs={a:enc(z) for a,z in [('p',p),('q',q),('r',r),('pr',pr),('qr',qr),('t',t)]},gap=str(gap),tested=total)
        (L/'threecluster-counterexample.json').write_text(json.dumps(o,indent=2));print(o);return
  print('threecluster degree',n,'triples',total,flush=True)
 (L/'threecluster-check.json').write_text(json.dumps(dict(tested=total,status='no certified strict violation',cache=len(cache)),indent=2))
run3()
