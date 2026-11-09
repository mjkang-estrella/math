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
basis=[]
for a in [1<<i for i in range(n)]:
 z=0
 for x in range(N):
  if a&x:z|=1<<x
 basis.append(z)
walsh=[0]
for z in basis:walsh += [v^z for v in walsh]
lo=int(sys.argv[4]) if len(sys.argv)>4 else 0
limit=min(lo+limit,1<<len(orbits));tt=0;prev=(lo-1)^((lo-1)>>1) if lo else 0;passed=0;found=[]
for j in range(len(orbits)):
 if prev>>j&1:tt^=orbits[j]
for m in range(lo,limit):
 if m and m%1000000==0:print(json.dumps({"completed":m}),flush=True)
 g=m^(m>>1)
 if m:tt^=orbits[(g^prev).bit_length()-1]
 prev=g
 if any(abs(N-2*(tt^z).bit_count()) != 1<<(n//2) for z in walsh[:32]):continue
 passed+=1
 for z in walsh[32:]:
  if abs(N-2*(tt^z).bit_count()) != 1<<(n//2):break
 else:found.append(g);break
print(json.dumps({'n':n,'degree':d,'orbit_count':len(orbits),'space':1<<len(orbits),'start':lo,'stop':m+1,'tested':m+1-lo,'selection':'binary-reflected Gray indices in [start,stop)','passed_first_32_Walsh':passed,'found':found,'seconds':time.time()-start}),flush=True)
