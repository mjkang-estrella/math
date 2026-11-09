import resource,os,math
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
for mode in ['fixed_t','center_shift']:
 found=False
 for n in range(4,31):
  f=[math.factorial(i) for i in range(n+1)]
  def v(t,x,y):return f[t+x]*f[n-t-x]+f[t+y]*f[n-t-y]+2*f[t+x+y]*f[n-t-x-y]-2*f[t+x]*f[y]*f[n-t-x-y]-2*f[t+y]*f[x]*f[n-t-x-y]
  for t in range(n-3):
   for x in range(2,n-t-1):
    for y in range(1,n-t-x):
     target=(t,x-1,y) if mode=='fixed_t' else (t+1,x-1,y)
     if v(*target)>v(t,x,y):print(mode,'counterexample',n,(t,x,y),v(t,x,y),'target',target,v(*target));found=True;break
    if found:break
   if found:break
  if found:break
 print(mode,'done',flush=True)
