from collections import Counter,defaultdict
import sys,json,itertools
N=int(sys.argv[1])
for n in range(3,N+1):
 tables=defaultdict(Counter);count=0;paths=0
 def pathsgen(g):
  if len(g)==n:
   if g.count(0)==2:yield g
   return
  for x in range(g[-1]+2):yield from pathsgen(g+[x])
 for g in pathsgen([0]):
  paths+=1;cut=g.index(0,1);comp=(cut,n-cut);area=sum(g)
  def labels(r,unused):
   k=len(r)
   if k==n:yield r;return
   low=r[-1] if k and g[k]==g[k-1]+1 else 0
   for x in unused:
    if x>low:yield from labels(r+[x],unused-{x})
  for r in labels([],set(range(1,n+1))):
   count+=1;di=tuple(r[i] for i in sorted(range(n),key=lambda i:(-g[i],r[i])));word=[r[i] for i in sorted(range(n),key=lambda i:(-g[i],-i))];pos={x:i for i,x in enumerate(word)};ides=sum(1<<x for x in range(1,n) if pos[x+1]<pos[x]);dinv=sum((g[i]==g[j] and r[i]<r[j]) or (g[i]+1==g[j] and r[i]>r[j]) for i in range(n) for j in range(i+1,n));tables[comp][di,area,ides,dinv]+=1
 failures=[]
 for b in range(1,(n-1)//2+1):
  a=n-b;res=Counter()
  for comp,shift,sign in [((a,b),0,1),((b+1,a-1),0,1),((b,a),1,-1),((a-1,b+1),1,-1)]:
   for (di,ar,ids,d),c in tables[comp].items():res[di,ar,ids,d+shift]+=sign*c
  bad=[(str(k),v) for k,v in res.items() if v]
  if bad:failures.append({'a':a,'b':b,'sample':bad[:1]})
 print(json.dumps({'n':n,'two_part_Dyck_paths':paths,'parking_functions_enumerated':count,'coefficient_keys':sum(map(len,tables.values())),'failures':failures}),flush=True)
