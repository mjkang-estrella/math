import os,resource,pathlib,json,random,time,itertools,fractions,math
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(50,50));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
p=pathlib.Path(__file__).resolve().parent;rng=random.Random(339860);out={'seed':339860,'edgecolor':[],'queens':[]};start=time.time()
def nu(n,edges):
 m=len(edges);match=[0]
 for j,(u,v) in enumerate(edges):
  b=1<<j;valid=[]
  for a in match:
   if all(not(a>>i&1) or not({u,v}&set(e)) for i,e in enumerate(edges[:j])):valid.append(a|b)
  match+=valid
 groups=[[] for _ in range(m)]
 for a in match[1:]:
  for j in range(m):
   if a>>j&1:groups[j].append(a)
 chi=bytearray(1<<m);values=[0]*(m+1)
 for a in range(1,1<<m):
  j=(a&-a).bit_length()-1
  c=1+min(chi[a^b] for b in groups[j] if a&b==b);chi[a]=c;values[c]=max(values[c],a.bit_count())
 for k in range(1,m+1):values[k]=max(values[k],values[k-1])
 return values, len(match)
for trial in range(48):
 n=7;edges=[(u,v) for u in range(3) for v in range(3,6) if rng.random()<.65]+[(u,6) for u in range(6) if rng.random()<.65]
 if len(edges)>13:continue
 vals,mc=nu(n,edges)
 failures=[{'k':k,'i':i} for k in range(1,len(vals)//2) for i in range(k+1) if 2*vals[k]<vals[k-i]+vals[k+i]-1]
 out['edgecolor'].append({'edges':edges,'nu':vals,'matchings':mc,'b_upper_bound':1,'defect1_failures':failures,'floor_failures':[k for k in range(1,len(vals)-1) if vals[k]<(vals[k-1]+vals[k+1])//2]})
(p/'diagnostics-edgecolor.json').write_text(json.dumps(out['edgecolor'],indent=2)+'\n');print('edgecolor',len(out['edgecolor']),time.time()-start,flush=True)
F=fractions.Fraction
def solve(rows,n):
 a=[[F(x) for x in row] for row in rows]
 for j in range(n):
  k=next((k for k in range(j,n) if a[k][j]),None)
  if k is None:return None
  a[j],a[k]=a[k],a[j];t=a[j][j];a[j]=[v/t for v in a[j]]
  for k in range(n):
   if k!=j and a[k][j]:
    t=a[k][j];a[k]=[x-t*y for x,y in zip(a[k],a[j])]
 return [a[j][-1] for j in range(n)]
for q in [8,10]:
 for trial in range(160):
  rows=[]
  for _ in range(3):
   row=[0]*(2*q+1);row[rng.randrange(2*q)]=1;row[-1]=rng.randrange(2);rows.append(row)
  for _ in range(2*q-3):
   i,j=rng.sample(range(q),2);dx,dy=rng.choice([(1,0),(0,1),(1,1),(1,-1)]);row=[0]*(2*q+1)
   row[2*i]=dx;row[2*j]=-dx;row[2*i+1]=dy;row[2*j+1]=-dy;rows.append(row)
  s=solve(rows,2*q)
  item={'q':q,'trial':trial,'singular':s is None}
  if s is not None:
   item.update(feasible=all(0<=x<=1 for x in s),denominator=math.lcm(*(x.denominator for x in s)),coordinates=list(map(str,s)),rows=rows)
  out['queens'].append(item)
(p/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print('done',time.time()-start,'queens',len(out['queens']),flush=True)
