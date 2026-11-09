# 378395 screen. For heights a in Z^{p x q} (normalised a[0][*]=a[*][0]=0, entries in 0..m), compute
# the vertices of Q(a)={(u,v): u_i+v_j >= -a_ij} modulo the shift (u+s,v-s): every vertex is the unique
# (mod shift) solution of u_i+v_j=-a_ij on some spanning tree of K_{p,q}; we enumerate spanning trees
# (via all functions assigning edges, filtered by connectivity), keep feasible solutions, dedupe.
# Tight graph G_w = edges tight at vertex w. L(a) = {a' : for every w, a'|G_w = x_i+y_j on G_w}.
# dim L(a) = nullity(system in a',x_w,y_w) - #V. a spans an extreme ray (coarsest subdivision) iff
# dim L(a) == p+q (lineality p+q-1 plus a itself) and a is not itself a lineality vector.
import itertools,sys,json
from fractions import Fraction
def rank_mod(rows,ncols,P=2147483647):
  A=[[x%P for x in r] for r in rows]; r=0
  for c in range(ncols):
    piv=next((i for i in range(r,len(A)) if A[i][c]),None)
    if piv is None: continue
    A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c],P-2,P); A[r]=[x*inv%P for x in A[r]]
    for i in range(len(A)):
      if i!=r and A[i][c]:
        f=A[i][c]; A[i]=[(x-f*y)%P for x,y in zip(A[i],A[r])]
    r+=1
  return r
def trees(p,q):
  E=[(i,j) for i in range(p) for j in range(q)]; n=p+q-1; out=[]
  for T in itertools.combinations(E,n):
    par=list(range(p+q))
    def f(x):
      while par[x]!=x: par[x]=par[par[x]]; x=par[x]
      return x
    ok=True
    for i,j in T:
      a,b=f(i),f(p+j)
      if a==b: ok=False;break
      par[a]=b
    if ok: out.append(T)
  return out
def vertices(a,p,q,TR):
  V={}
  for T in TR:
    u=[None]*p; v=[None]*q; u[0]=Fraction(0); adj={}
    for i,j in T: adj.setdefault(('u',i),[]).append(('v',j)); adj.setdefault(('v',j),[]).append(('u',i))
    st=[('u',0)]
    while st:
      x=st.pop()
      for y in adj.get(x,[]):
        if y[0]=='v' and v[y[1]] is None: v[y[1]]=-a[x[1]][y[1]]-u[x[1]]; st.append(y)
        if y[0]=='u' and u[y[1]] is None: u[y[1]]=-a[y[1]][x[1]]-v[x[1]]; st.append(y)
    if all(u[i]+v[j]+a[i][j]>=0 for i in range(p) for j in range(q)):
      V[(tuple(u),tuple(v))]=frozenset((i,j) for i in range(p) for j in range(q) if u[i]+v[j]+a[i][j]==0)
  return V
def dimL(V,p,q):
  W=list(V.values()); nv=p*q+len(W)*(p+q); rows=[]
  for k,G in enumerate(W):
    for i,j in G:
      r=[0]*nv; r[i*q+j]=1; r[p*q+k*(p+q)+i]=-1; r[p*q+k*(p+q)+p+j]=-1; rows.append(r)
  return nv-rank_mod(rows,nv)-len(W)
def is_lineality(a,p,q): return all(a[i][j]-a[i][0]-a[0][j]+a[0][0]==0 for i in range(p) for j in range(q))
if __name__=='__main__':
  p,q,m=map(int,sys.argv[1:4]); TR=trees(p,q); free=[(i,j) for i in range(1,p) for j in range(1,q)]
  stats={}; rays=[]; nconf=0
  for vals in itertools.product(range(m+1),repeat=len(free)):
    a=[[0]*q for _ in range(p)]
    for (i,j),x in zip(free,vals): a[i][j]=x
    nconf+=1
    if is_lineality(a,p,q): continue
    V=vertices(a,p,q,TR); d=dimL(V,p,q)
    if d==p+q:
      key=len(V); stats[key]=stats.get(key,0)+1
      if key>q or len(rays)<3: rays.append(dict(a=a,cells=len(V)))
  print(json.dumps(dict(p=p,q=q,m=m,configs=nconf,trees=len(TR),ray_cellcount_histogram=stats,examples=[r for r in rays if r['cells']>q][:5],first=rays[:3])))
