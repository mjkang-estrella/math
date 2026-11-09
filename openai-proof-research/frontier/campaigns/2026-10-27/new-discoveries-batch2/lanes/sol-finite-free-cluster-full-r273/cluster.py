from pathlib import Path
import sympy as S,json,itertools,math,time,sys
L=Path(__file__).resolve().parent;x=S.Symbol('x');Q=S.Rational
def convolution(p,q,n):
 return S.Poly(sum(S.diff(p.as_expr(),x,k)*q.nth(n-k)*math.factorial(n-k) for k in range(n+1))/math.factorial(n),x)
def cluster(n,a,u):return S.Poly(x**(n-a)*(x-u)**a,x)
cache={}
def roots(p):
 key=tuple(p.all_coeffs())
 if key not in cache:
  iv=p.intervals(eps=Q(1,10**9));assert sum(m for _,m in iv)==p.degree()
  cache[key]=list(reversed([ab for ab,m in iv for _ in range(m)]))
 return cache[key]
def enc(p):return [str(t) for t in p.all_coeffs()]
def run():
 total=0;gaps=[]
 scales=[Q(1,4),Q(1),Q(4)] if '--moderate' in sys.argv else [Q(1,100),Q(1),Q(100)]
 for n in range(3,7):
  for a,b,c in itertools.product(range(1,n),repeat=3):
   for v,w in itertools.product(scales,repeat=2):
    p=cluster(n,a,1);q=cluster(n,b,v);r=cluster(n,c,w)
    pr=convolution(p,r,n);qr=convolution(q,r,n);t=convolution(pr,q,n)
    T,A,B,C=map(roots,[t,pr,qr,r]);total+=1
    for j in range(1,n+1):
     for k in range(1,n+2-j):
      i=j+k-1
      for label,l in [('max',max(j,k)),('reflected',n+1-max(j,k))]:
       lo=T[i-1][0]+C[l-1][0]-A[j-1][1]-B[k-1][1]
       hi=T[i-1][1]+C[l-1][1]-A[j-1][0]-B[k-1][0]
       if lo>0:
        out=dict(n=n,a=a,b=b,c=c,v=str(v),w=str(w),i=i,j=j,k=k,l=l,branch=label,lower_gap=str(lo),upper_gap=str(hi),coeffs={name:enc(z) for name,z in [('p',p),('q',q),('r',r),('pr',pr),('qr',qr),('t',t)]},intervals={name:[[str(s) for s in ab] for ab in z] for name,z in [('t',T),('pr',A),('qr',B),('r',C)]},tested=total)
        (L/'counterexample.json').write_text(json.dumps(out,indent=2));print(json.dumps(out));return
  print('degree completed',n,'triples',total,flush=True)
 (L/('cluster-check.json' if '--moderate' in sys.argv else 'separated-cluster-check.json')).write_text(json.dumps(dict(tested=total,scales=list(map(str,scales)),status='no certified strict violation',cache=len(cache),root_isolation='exact rational SymPy intervals, epsilon=1e-9; unknown interval signs are not certified positive'),indent=2))
if __name__=='__main__':run()
