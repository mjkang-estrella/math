import itertools,json,time,sys,math
n=int(sys.argv[1]);start=time.monotonic();orients=list(itertools.product([0,1],repeat=n-2));counts=[0]*len(orients);cats=[0]*len(orients);forbidden=[]
for ori in orients:
 edges=[(i,i+1) if a==0 else (i+1,i) for i,a in enumerate(ori)];word=[]
 while len(word)<n-1:word.append(min(i for i in range(n-1) if i not in word and all(a in word for a,b in edges if b==i)))
 c=list(range(n))
 for i in word:c[i],c[i+1]=c[i+1],c[i]
 forbidden.append([(i,j) for i in range(n) for j in range(i+1,n) if c[i]>c[j]])
firsts=range(int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else range(n)
for w in ((f,)+v for f in firsts for v in itertools.permutations([i for i in range(n) if i!=f])):
 req={};bad=False
 for i in range(n):
  for j in range(i+1,n):
   for k in range(j+1,n):
    a,b,c=w[i],w[j],w[k]
    if b>a>c:v=a;bit=0
    elif a>c>b:v=c;bit=1
    else:continue
    if v-1 in req and req[v-1]!=bit:bad=True;break
    req[v-1]=bit
   if bad:break
  if bad:break
 if bad:continue
 pos=[w.index(i) for i in range(n)];des=[i for i in range(n-1) if w[i]>w[i+1]];commute=all(b-a!=1 for a,b in zip(des,des[1:]))
 for idx,ori in enumerate(orients):
  if any(ori[j]!=v for j,v in req.items()):continue
  cats[idx]+=1
  if commute and not any(pos[i]>pos[j] for i,j in forbidden[idx]):counts[idx]+=1
print(json.dumps({'rank':n-1,'first_values':list(firsts),'permutations':len(firsts)*math.factorial(n-1),'orientations':len(orients),'catalan_counts':cats,'image_counts':counts,'linear':counts[0],'bipartite':next(counts[i] for i,o in enumerate(orients) if all(a!=b for a,b in zip(o,o[1:]))),'min':min(counts),'max':max(counts),'seconds':time.monotonic()-start}),flush=True)
