import sys,itertools,time,json
n=int(sys.argv[1]);d=int(sys.argv[2]);limit=int(sys.argv[3]);N=1<<n;seen=set();orbits=[];start=time.time()
for c in itertools.combinations(range(n),d):
 s=sum(1<<i for i in c)
 if s in seen:continue
 o=[];t=s
 while t not in o:o.append(t);seen.add(t);t=((t<<1)&(N-1))|(t>>(n-1))
 # make truth table by XORing monomial masks
 tt=0
 for m in o:
  z=0
  for x in range(N):
   if x&m==m:z|=1<<x
  tt^=z
 orbits.append(tt)
walsh=[]
for a in range(min(N,32)):
 z=0
 for x in range(N):
  if (a&x).bit_count()%2:z|=1<<x
 walsh.append(z)
limit=min(limit,1<<len(orbits));tt=0;prev=0;passed=0;found=[]
for m in range(limit):
 g=m^(m>>1)
 if m:tt^=orbits[(g^prev).bit_length()-1]
 prev=g
 if any(abs(N-2*(tt^z).bit_count()) != 1<<(n//2) for z in walsh):continue
 passed+=1
 for a in range(32,N):
  z=0
  for x in range(N):
   if (a&x).bit_count()%2:z|=1<<x
  if abs(N-2*(tt^z).bit_count()) != 1<<(n//2):break
 else:found.append(g);break
print(json.dumps({'n':n,'degree':d,'orbit_count':len(orbits),'space':1<<len(orbits),'tested':m+1,'selection':'initial binary-reflected Gray prefix of orbit coefficient masks','passed_first_32_Walsh':passed,'found':found,'seconds':time.time()-start}),flush=True)
