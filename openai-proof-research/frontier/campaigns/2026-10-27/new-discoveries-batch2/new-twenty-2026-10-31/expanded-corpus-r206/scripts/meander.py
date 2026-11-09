import pathlib,sys,itertools,json
D=pathlib.Path(__file__).resolve().parents[1]
def partitions(n):
 if n==0:return [()]
 out=[]
 # recursive block containing 0; independent gaps
 for mask in range(1<<(n-1)):
  block=[0]+[i+1 for i in range(n-1) if mask>>i&1];ends=block[1:]+[n];gaps=[partitions(e-b-1) for b,e in zip(block,ends)]
  for pieces in itertools.product(*gaps):
   p=list(range(n))
   for a,b in zip(block,block[1:]+block[:1]):p[a]=b
   for start,piece in zip(block,pieces):
    for i,v in enumerate(piece):p[start+1+i]=start+1+v
   out.append(tuple(p))
 return out
for n in range(1,int(sys.argv[1])+1):
 ps=partitions(n);inv=[]
 for p in ps:
  q=[0]*n
  for i,v in enumerate(p):q[v]=i
  inv.append(q)
 cnt=[0]*len(ps)
 for i,p in enumerate(ps):
  for j in range(i+1,len(ps)):
   q=inv[j];x=p[q[0]];k=1
   while x:x=p[q[x]];k+=1
   if k==n:cnt[i]+=1;cnt[j]+=1
 if n==1:cnt=[1]
 r=tuple(n-1-i for i in range(n));best=max(cnt);orbit=set();p=r
 # K(p)=p^-1 cycle
 while p not in orbit:
  orbit.add(p);q=[0]*n
  for i,v in enumerate(p):q[v]=i
  p=tuple(q[(i+1)%n] for i in range(n))
 maximizers={p for p,c in zip(ps,cnt) if c==best}
 rec={'n':n,'partitions':len(ps),'pairs':len(ps)*(len(ps)-1)//2,'maximum':best,'rainbow':cnt[ps.index(r)],'maximizers':len(maximizers),'kreweras_orbit':len(orbit),'exact_set_equal':maximizers==orbit};print(json.dumps(rec),flush=True)
 (D/f'outputs/meander-n{n}.json').write_text(json.dumps(rec,indent=2)+'\n')
