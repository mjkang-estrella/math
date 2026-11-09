import itertools,json,time,sys
N=int(sys.argv[1]) if len(sys.argv)>1 else 7
for n in range(2,N+1):
 counts=[];start=time.monotonic()
 for orient in itertools.product([0,1],repeat=n-2):
  edges=[(i,i+1) if a==0 else (i+1,i) for i,a in enumerate(orient)];word=[]
  while len(word)<n-1:word.append(min(i for i in range(n-1) if i not in word and all(a in word for a,b in edges if b==i)))
  c=list(range(n))
  for i in word:c[i],c[i+1]=c[i+1],c[i]
  ci=[c.index(i) for i in range(n)];cileft={(i,j) for i in range(n) for j in range(i+1,n) if c[i]>c[j]} # inverse positions in c^-1 = c
  total=0;sortable_count=0
  for w in itertools.permutations(range(n)):
   pos=[w.index(i) for i in range(n)];pp=pos[:];last=(1<<(n-1))-1;sort=True
   while any(pp[i]>pp[i+1] for i in range(n-1)):
    cur=0
    for i in word:
     if pp[i]>pp[i+1]:cur|=1<<i;pp[i],pp[i+1]=pp[i+1],pp[i]
    if cur&~last:sort=False;break
    last=cur
   if not sort:continue
   sortable_count+=1
   des=[i for i in range(n-1) if w[i]>w[i+1]]
   if any(b-a==1 for a,b in zip(des,des[1:])):continue
   if any(pos[i]>pos[j] for i,j in cileft):continue
   total+=1
  counts.append({'orientation':orient,'coxeter_word':word,'sortable':sortable_count,'image':total})
 lo=counts[0]['image'];bi=next(x['image'] for x in counts if all(a!=b for a,b in zip(x['orientation'],x['orientation'][1:])))
 print(json.dumps({'rank':n-1,'permutations_per_orientation':__import__('math').factorial(n),'linear':lo,'bipartite':bi,'min':min(x['image'] for x in counts),'max':max(x['image'] for x in counts),'orientations':counts,'seconds':time.monotonic()-start}),flush=True)
