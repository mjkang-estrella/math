import itertools,functools,json,sys
R=int(sys.argv[1]);P=int(sys.argv[2]);complete_only=len(sys.argv)>3;roots=list(itertools.combinations(range(R+1),2));z=(0,)*len(roots)
@functools.lru_cache(None)
def sig(a,i,star):
 order=sorted(range(len(roots)),key=lambda j:(roots[j][1],-roots[j][0]) if star else (-roots[j][0],roots[j][1]))
 stack=[]
 for j in order:
  x,y=roots[j];sg= (1 if x==i+1 else -1 if x==i else 0) if star else (1 if y==i else -1 if y==i+1 else 0)
  for _ in range(a[j] if sg else 0):
   if sg==1 and stack and stack[-1][0]==-1:stack.pop()
   else:stack.append((sg,j))
 return tuple(stack)
@functools.lru_cache(None)
def e(a,i):
 normal=sig(a,i,False);star=sig(a,i,True);an=sum(s==1 for s,j in normal);bs=sum(s==-1 for s,j in star)
 ss=normal if bs<=an else star;minus=[j for s,j in ss if s==-1]
 if not minus:return None,False
 j=minus[0];x,y=roots[j]
 if (x,y)==(i,i+1):return None,True
 new=list(a);new[j]-=1;new[roots.index((x,y-1) if bs<=an else (x+1,y))]+=1
 return tuple(new),False
def path(a,seq):
 for i in seq:
  a,broken=e(a,i)
  if a is None:return None
 return a
def bd(a,i):
 x,_=e(a,i);y,_=e(a,i+1)
 return x is not None and y is not None and e(x,i+1)[1] and e(y,i)[1]
def comps(n,k):
 if k==1:yield(n,);return
 for a in range(n+1):
  for rest in comps(n-a,k-1):yield(a,)+rest
num=eligible=steps=0;bad=[]
for total in range(P+1):
 for a in comps(total,len(roots)):
  num+=1;w=[0]*(R+1)
  for c,(x,y) in zip(a,roots):w[x]+=c;w[y]-=c
  for i in range(R-1):
   for k in range(max(1,w[i]-w[i+1]+1),P+1):
    for l in range(max(1,w[i+1]-w[i+2]+1),P+1):
     if path(a,[i]*k) is None or path(a,[i+1]*l) is None:continue
     eligible+=1
     for seq in [[i]*k+[i+1]*(k+l)+[i]*l,[i+1]*l+[i]*(k+l)+[i+1]*k]:
      if complete_only and path(a,seq) is None:continue
      b=a
      for j in seq:
       if bd(b,i):bad.append([a,i,k,l,b]);break
       b,_=e(b,j);steps+=1
       if b is None:break
 print(json.dumps(dict(rank=R,total_parts_through=total,partitions=num,eligible_hexagons=eligible,steps=steps,bd_first=bad[:3],cache=e.cache_info()._asdict())),flush=True)
 if bad:break
