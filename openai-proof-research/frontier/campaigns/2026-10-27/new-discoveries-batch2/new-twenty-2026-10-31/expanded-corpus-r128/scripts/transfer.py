import random,math,sys
rng=random.Random(128)
for n,m in [(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)]:
 pts=[(i,j)for i in range(n+1)for j in range(m+1)];idx={p:i for i,p in enumerate(pts)};s=len(pts)
 below=[[c for c,(x,y)in enumerate(pts)if x<=b[0]and y<=b[1]]for b in pts]
 arrows=[(a,b)for b in range(s)for a in below[b]if a!=b]
 rest={}
 for a,b in arrows:
  rest[a,b]=[(idx[min(pts[a][0],pts[c][0]),min(pts[a][1],pts[c][1])],c)for c in below[b]]
 def closure(es):
  rows=[1<<a for a in range(s)]
  for a,b in es:rows[a]|=1<<b
  changed=True
  while changed:
   old=rows[:]
   for a,b in arrows:
    if rows[a]>>b&1:
     for c,d in rest[a,b]:rows[c]|=1<<d
   for b in range(s):
    for a in range(s):
     if rows[a]>>b&1:rows[a]|=rows[b]
   changed=rows!=old
  return tuple(rows)
 if m==2 and n%2==0:pred=1+3*n
 elif (n+m)%2==0:pred=math.comb(m+3,3)-((m+2)//2)*((m+3)//2)+(n-m)//2*math.comb(m+2,2)
 else:pred=math.comb(m+3,3)+(n-m-1)//2*math.comb(m+2,2)
 best=0
 for trial in range(120):
  prob=rng.uniform(.03,.6);gen=[e for e in arrows if rng.random()<prob];rng.shuffle(gen);target=closure(gen)
  for e in gen[:]:
   cand=gen[:];cand.remove(e)
   if closure(cand)==target:gen=cand
  best=max(best,len(gen))
  if len(gen)>pred:print('WITNESS',n,m,gen,pred,flush=True);break
 print(dict(n=n,m=m,trials=trial+1,arrows=len(arrows),max_minimal_basis_found=best,conjectured=pred,coverage='seeded random transfer systems, redundancy fully checked by closure'),flush=True)
