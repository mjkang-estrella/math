import random,json,sys
rng=random.Random(222)
for N in [20,24,30,40,60,80,100]:
 count=tries=over=0;mx=0;f=[0,1]
 for _ in range(N):f.append(sum(f[-2:]))
 bound=f[N//2+2]+1
 for z in range(10000):
  d=[2]+[1]*(N-2)+[2];E=list(zip(range(N-1),range(1,N)));ok=True;tries+=1
  for i in range(N):
   opts=[j for j in range(i+2,N) if d[j]]
   if len(opts)<d[i]:ok=False;break
   # Structured short-jump bias in three quarters of trials; otherwise uniform.
   J=[]
   for _ in range(d[i]):
    if z%4:
     w=[1/(j-i)**(1+z%3) for j in opts];j=rng.choices(opts,w)[0]
    else:j=rng.choice(opts)
    opts.remove(j);J.append(j)
   for j in J:d[j]-=1;E.append((i,j))
   d[i]=0
  if not ok:continue
  count+=1;p=[0]*N;p[0]=1;a=[[] for _ in range(N)]
  for i,j in E:a[i].append(j)
  for i in range(N):
   for j in a[i]:p[j]+=p[i]
  mx=max(mx,p[-1]);over+=p[-1]>bound
 print(json.dumps({'vertices':N,'attempts':tries,'completed':count,'bound':bound,'unfiltered_max_paths':mx,'overbound_needing_connectivity_check':over}),flush=True)
