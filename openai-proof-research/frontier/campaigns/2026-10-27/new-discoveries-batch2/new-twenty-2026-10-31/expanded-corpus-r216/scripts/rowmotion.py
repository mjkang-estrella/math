import sys,json
m,n=map(int,sys.argv[1:]);N=m*n
ideals=[]
def gen(i,prev,s):
 if i==m:ideals.append(s);return
 for k in range(prev+1):gen(i+1,k,s|(((1<<k)-1)<<(i*n)))
gen(0,n,0)
allsets={a&~b for a in ideals for b in ideals if not b&~a}
print('grid',m,n,'ideals',len(ideals),'convex_sets',len(allsets),flush=True)
lo=[];hi=[]
for x in range(N):
 lo.append(sum(1<<y for y in range(N) if y!=x and y//n<=x//n and y%n<=x%n))
 hi.append(sum(1<<y for y in range(N) if y!=x and y//n>=x//n and y%n>=x%n))
def stat(s):
 t=s;v=0
 while t:
  b=t&-t;x=b.bit_length()-1;t-=b;v+=int(not s&hi[x])-int(not s&lo[x])
 return v
bits=[1<<x for x in reversed(range(N))]; unseen=set(allsets);orbits=0;longest=0
while unseen:
 a=next(iter(unseen));s=a;v=0;length=0
 while True:
  unseen.remove(s);v+=stat(s);length+=1
  for b in bits:
   if s^b in allsets:s^=b
  if s==a:break
 orbits+=1;longest=max(longest,length)
 if v:
  print('COUNTEREXAMPLE',a,length,v,flush=True);sys.exit(1)
print('PASS',m,n,'states',len(allsets),'orbits',orbits,'longest',longest,flush=True)
