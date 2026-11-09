import json,pathlib,itertools
lane=pathlib.Path(__file__).resolve().parents[1]
def graph(m,n):
 return {(a*n+b,c*n+d) for a,b,c,d in itertools.product(range(m),range(n),range(m),range(n)) if a*n+b<c*n+d and ((a==c and (b-d)%n in (1,n-1)) or (b==d and (a-c)%m in (1,m-1)))}
def weights(E,M,N):
 S=set(M); order=[]
 while S:
  V={v for e in S for v in e};deg={v:sum(v in e and set(e)<=V for e in E) for v in V}
  e=next(e for e in sorted(S) if any(deg[v]==1 for v in e));a,b=e
  if deg[a]!=1:a,b=b,a
  order.append((a,b));S.remove(e)
 w={}
 for a,b in reversed(order):
  w[b]=-1-max([abs(x) for x in w.values()]+[0]);w[a]=1-w[b]
 t=-1-max([abs(x) for x in w.values()]+[0]); w=[w.get(i,t) for i in range(N)]
 assert all((w[a]+w[b]>0 if (a,b) in M else w[a]+w[b]<0) for a,b in E)
 return w,order
for p in sorted((lane/'logs').glob('search-*.json')):
 d=json.loads(p.read_text());parts=d.get('five_parts')
 if parts is None:continue
 m,n=d['m'],d['n'];E=graph(m,n);stages=[]
 for part in parts:
  M={tuple(e) for e in part};assert M<=E;assert len({v for e in M for v in e})==2*len(M)
  w,peel=weights(E,M,m*n);stages.append({'matching':sorted(M),'weights':w,'peel_order':peel});E-=M
 assert not E
 (lane/'logs'/('independent-'+p.name)).write_text(json.dumps({'m':m,'n':n,'stages':stages,'all_strict_signs_checked':True},indent=2)+'\n')
 print(m,n,'PASS independent integer weights, partition and matching verification')
