"""Exact rational power-cell tests. Finite diagnostics, never an analytic proof."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json, hashlib

ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i33_density_robust_brenier'
BOX=[(F(-1),F(-1)),(F(1),F(-1)),(F(1),F(1)),(F(-1),F(1))]

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def clip(poly,n,b):
 if not poly:return []
 ans=[]
 for p,q in zip(poly,poly[1:]+poly[:1]):
  u,v=dot(n,p)+b,dot(n,q)+b
  if u>=0:ans.append(p)
  if (u<0<v) or (v<0<u):
   t=u/(u-v);ans.append(tuple(p[k]+t*(q[k]-p[k]) for k in range(2)))
 unique=[]
 for p in ans:
  if not unique or p!=unique[-1]:unique.append(p)
 if len(unique)>1 and unique[0]==unique[-1]:unique.pop()
 return unique if len(unique)>=3 else []

def cells(sites,c):
 ans=[]
 for i,y in enumerate(sites):
  p=BOX[:]
  for j,z in enumerate(sites):
   if i!=j:p=clip(p,sub(y,z),c[i]-c[j])
  ans.append(p)
 return ans

def conv(a,b):
 r=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return r
def linpow(a,b,n):return [F(comb(n,k))*a**(n-k)*b**k for k in range(n+1)]
def edgeint(p,q,i,j):
 a=conv(linpow(p[0],q[0]-p[0],i),linpow(p[1],q[1]-p[1],j))
 return sum(x/F(k+1) for k,x in enumerate(a))
def monomial(poly,i,j):
 return sum((q[1]-p[1])*edgeint(p,q,i+1,j)/F(i+1) for p,q in zip(poly,poly[1:]+poly[:1])) if poly else F(0)
def integrate(poly,density,shift=(0,0)):
 return sum(c*monomial(poly,i+shift[0],j+shift[1]) for (i,j),c in density.items())
def cheb(n):
 a,b=[F(1)],[F(0),F(1)]
 if n==0:return a
 for _ in range(1,n):
  r=[F(0)]+[2*x for x in b]
  for k,v in enumerate(a):r[k]-=v
  a,b=b,r
 return b
def density(n):return {(0,0):F(1,4),**{(i,1):x/8 for i,x in enumerate(cheb(n)) if x}}

def facet(poly,n,b):
 pts=[p for p in poly if dot(n,p)+b==0]
 if len(pts)<2:return None
 return max(((p,q) for p in pts for q in pts),key=lambda pq:dot(sub(pq[1],pq[0]),sub(pq[1],pq[0])))
def operators(sites,c,polys,dens):
 n=len(sites); g=[[F(0)]*n for _ in sites];b=[[[F(0),F(0)] for _ in sites] for _ in sites]
 for i in range(n):
  for j in range(i+1,n):
   normal=sub(sites[i],sites[j]);face=facet(polys[i],normal,c[i]-c[j])
   if not face:continue
   p,q=face;d=sub(q,p);rot=(-normal[1],normal[0]);scale=abs(dot(d,rot))/dot(normal,normal)
   g[i][j]=g[j][i]=scale*sum(v*edgeint(p,q,k,l) for (k,l),v in dens.items())
   for z in range(2): b[i][j][z]=b[j][i][z]=scale*sum(v*edgeint(p,q,k+(z==0),l+(z==1)) for (k,l),v in dens.items())
 return g,b

def transport_cost(m,n,a,b):
 """Exact min-cost flow on a complete bipartite network; Bellman-Ford residual paths."""
 na,nb=len(a),len(b);N=na+nb+2;s=N-2;t=N-1;adj=[[] for _ in range(N)]
 def edge(u,v,cap,cost):
  adj[u].append([v,len(adj[v]),cap,cost]);adj[v].append([u,len(adj[u])-1,F(0),-cost])
 for i,x in enumerate(m):edge(s,i,x,F(0))
 for j,x in enumerate(n):edge(na+j,t,x,F(0))
 for i,y in enumerate(a):
  for j,z in enumerate(b):edge(i,na+j,F(1),dot(sub(y,z),sub(y,z)))
 result=F(0);sent=F(0)
 while sent<1:
  dist=[None]*N;prev=[None]*N;dist[s]=F(0)
  for _ in range(N-1):
   changed=False
   for u in range(N):
    if dist[u] is None:continue
    for k,(v,_,cap,cost) in enumerate(adj[u]):
     if cap>0 and (dist[v] is None or dist[v]>dist[u]+cost):dist[v]=dist[u]+cost;prev[v]=(u,k);changed=True
   if not changed:break
  assert dist[t] is not None
  amt=1-sent;v=t;visited=set()
  while v!=s:
   assert v not in visited;visited.add(v);u,k=prev[v];amt=min(amt,adj[u][k][2]);v=u
  v=t
  while v!=s:
   u,k=prev[v];e=adj[u][k];e[2]-=amt;adj[v][e[1]][2]+=amt;v=u
  sent+=amt;result+=amt*dist[t]
 return result

def graph_tests():
 cases=[]
 configs=[]
 for size in (2,3):
  sites=[(F(2*i-size+1,size),F(2*j-size+1,size)) for i in range(size) for j in range(size)]
  configs.append(('grid'+str(size),sites,[-dot(y,y)/2 for y in sites]))
 ring=[(F(3,4),F(0)),(F(1,2),F(1,2)),(F(-1,2),F(1,2)),(F(-3,4),F(0)),(F(-1,2),F(-1,2)),(F(1,2),F(-1,2)),(F(0),F(0))]
 configs.append(('cycle6',ring,[-dot(y,y)/2 for y in ring]))
 for a in (F(1,8),F(1,32),F(1,128)):
  for lam in (F(1),F(1,64)):
   configs.append(('thin_'+str(a)+'_scale_'+str(lam),[(-lam,F(0)),(F(0),F(0)),(lam,F(0))],[F(0),lam*a,F(0)]))
 for name,sites,c in configs:
  polys=cells(sites,c)
  for degree in (1,3,7):
   dens=density(degree);m=[integrate(p,dens) for p in polys]
   assert sum(m)==1 and min(m)>0
   g,b=operators(sites,c,polys,dens)
   edges=sum(g[i][j]>0 for i in range(len(m)) for j in range(i+1,len(m)))
   qs=[[y[0] for y in sites],[y[1] for y in sites],[F((-1)**i) for i in range(len(m))],[F((17*i+3)%11-5) for i in range(len(m))]]
   for q in qs:
    dm=[sum(g[i][j]*(q[i]-q[j]) for j in range(len(m))) for i in range(len(m))]
    db=[tuple(sum(b[i][j][k]*(q[i]-q[j]) for j in range(len(m))) for k in range(2)) for i in range(len(m))]
    assert sum(dm)==0 and all(sum(z[k] for z in db)==0 for k in range(2))
    em=sum(x*x/z for x,z in zip(dm,m));eb=sum(dot(x,x)/z for x,z in zip(db,m))
    if em:cases.append({'name':name,'degree':degree,'N':len(m),'edges':edges,'ratio':str(eb/em)})
 return cases,configs

def map_tests(configs):
 rows=[]
 for name,sites,c in configs:
  # Uniform scaling of all slopes and intercepts preserves cells. Include nonuniform site tilts.
  for eps in (F(1,128),F(1,512)):
   v=[(F(((3*i)%5)-2)*eps,F(((7*i)%5)-2)*eps) for i in range(len(sites))]
   new=[tuple(y[k]+z[k] for k in range(2)) for y,z in zip(sites,v)]
   if len(set(new))!=len(new):continue
   cc=[x+eps*F((i%3)-1,3) for i,x in enumerate(c)]
   if name=='thin_1/8_scale_1' and eps==F(1,128):
    cc[1]=F(-2)  # Deliberately delete a cell and its target atom.
   p0,p1=cells(sites,c),cells(new,cc)
   dens=density(3);m=[integrate(p,dens) for p in p0];n=[integrate(p,dens) for p in p1]
   assert sum(m)==sum(n)==1 and min(n)>=0
   err=F(0)
   for i,poly in enumerate(p0):
    for j,y in enumerate(new):
     p=poly
     for k,z in enumerate(new):
      if k!=j:p=clip(p,sub(y,z),cc[j]-cc[k])
     err+=integrate(p,dens)*dot(sub(sites[i],y),sub(sites[i],y))
   cost=transport_cost(m,n,sites,new)
   assert cost<=err
   rows.append({'name':name,'eps':str(eps),'N':len(sites),'squared_map_error':str(err),'W2_squared':str(cost),'D6_over_W2_squared':str(err**3/cost) if cost else None,'zero_cells':sum(x==0 for x in n)})
 return rows

def closed_form_tests():
 rows=[]
 for k in range(2,17):
  a=F(1,2**k)
  for kap in (F(1,4),F(1,2),F(3,4)):
   m=[(1-a)/2,a,(1-a)/2];dm=[F(-1,2),F(0),F(1,2)];db=[(a/2,kap/6),(-a,-kap/3),(a/2,kap/6)]
   em=sum(x*x/z for x,z in zip(dm,m));eb=sum(dot(x,x)/z for x,z in zip(db,m))
   assert em==1/(1-a) and eb/em==a+kap*kap/(9*a)
   vel=[-kap/3,F(0),kap/3]
   g=F(1,2);by=[-kap/6,kap/6]
   assert g*(vel[0]-vel[1])-by[0]==0 and g*(vel[2]-vel[1])-by[1]==0
   variance=(1-a)*kap*kap/9+a/3
   rows.append({'a':str(a),'kappa':str(kap),'moment_ratio':str(eb/em),'potential_speed_ratio_squared':str(variance/a)})
 # Exact conditioning and Moreau obstruction identities.
 for k in range(2,40):
  h=F(1,2**k);error=4*h;gap=h*h
  assert error*error==16*gap
  # Integral 1/(2h) int_0^h (h-x)^2 dx.
  assert (h*h*h-h*h*h+h*h*h/3)/(2*h)==h*h/6
 # DAG transfer bound by sorting intercept changes. Exercise all chains and shortcuts.
 dag_count=0
 for n in range(2,18):
  for seed in range(8):
   flow={(i,j):F((i*11+j*7+seed)%5,113) for i in range(n) for j in range(i+1,n)}
   div=[sum(v for (i,j),v in flow.items() if j==k)-sum(v for (i,j),v in flow.items() if i==k) for k in range(n)]
   moved=sum(flow.values());tv=sum(max(x,0) for x in div)
   assert moved<=(n-1)*tv;dag_count+=1
 return rows,dag_count

def run():
 closed,dag=closed_form_tests();graphs,configs=graph_tests();maps=map_tests(configs)
 result={'scope':'exact rational finite diagnostics, not universal proof','closed_form_cases':closed,'dag_cases':dag,'facet_cases':graphs,'transport_cases':maps,'summary':{'closed_form':len(closed),'dag':dag,'facets':len(graphs),'transports':len(maps),'max_map_ratio_float':max(float(F(r['D6_over_W2_squared'])) for r in maps)}}
 data=json.dumps(result,indent=2)+'\n';(OUT/'diagnostics.json').write_text(data)
 print(json.dumps(result['summary'],sort_keys=True))

if __name__=='__main__':run()
