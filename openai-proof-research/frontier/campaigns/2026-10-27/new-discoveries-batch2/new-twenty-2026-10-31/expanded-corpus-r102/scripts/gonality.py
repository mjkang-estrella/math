import itertools,math,json,time,functools
@functools.cache
def comps(d,n):
 if n==1:return [(d,)]
 return [(a,)+v for a in range(d+1) for v in comps(d-a,n-1)]
def det(a):
 if not a:return 1
 return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))
def test(n,es,ms):
 L=[[0]*n for _ in range(n)]
 for (a,b),m in zip(es,ms):L[a][a]+=m;L[b][b]+=m;L[a][b]-=m;L[b][a]-=m
 A=[r[:-1] for r in L[:-1]];den=det(A)
 if not den:return None
 adj=[[(-1)**(i+j)*det([r[:i]+r[i+1:] for k,r in enumerate(A) if k!=j]) for j in range(n-1)]for i in range(n-1)]
 def cls(v):return tuple(sum(a*b for a,b in zip(row,v))%den for row in adj)
 def sub(a,b):return tuple((x-y)%den for x,y in zip(a,b))
 C=[{cls(v) for v in comps(d,n)} for d in range(2*n+1)]
 E=[list(C[r]) for r in range(3)]
 gons=[];div2=[]
 for r in [1,2]:
  for d in range(r,2*n+1):
   good=[v for v in comps(d,n) if all(sub(cls(v),e) in C[d-r] for e in E[r])]
   if good:gons.append(d);div2=good;break
 if gons[1]!=gons[0]+1:return {'tight':False}
 k=gons[0];g=sum(ms)-n+1;can=tuple(L[i][i]-2 for i in range(n));bad=[v for v in div2 if cls(tuple((k-2)*x-y for x,y in zip(v,can)))!=cls((0,)*n)] if g==k*(k-1)//2 else []
 return {'tight':True,'k':k,'g':g,'degree2':gons[1],'genus_fail':g!=k*(k-1)//2,'canonical_fail':bad,'edges':list(zip(es,ms))}
for n,mm in [(2,8),(3,5),(4,3),(5,1)]:
 es=list(itertools.combinations(range(n),2));count=0;tight=[];start=time.monotonic()
 for ms in itertools.product(range(mm+1),repeat=len(es)):
  o=test(n,es,ms)
  if o is None:continue
  count+=1
  if o['tight']:tight.append(o)
 print(json.dumps({'n':n,'multiplicity_cap':mm,'connected_labelled':count,'tight_count':len(tight),'tight':tight,'seconds':time.monotonic()-start}),flush=True)
