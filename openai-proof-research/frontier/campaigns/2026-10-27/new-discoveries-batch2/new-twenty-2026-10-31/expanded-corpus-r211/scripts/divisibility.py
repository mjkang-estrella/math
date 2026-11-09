import pathlib,json,math,sys,collections
D=pathlib.Path(__file__).resolve().parents[1]
def parts(n,lo=1):
 if n==0:yield ()
 for k in range(lo,n+1):
  for r in parts(n-k,k):yield (k,)+r
def diameter(v):
 n=len(v);adj=[0]*n
 for i in range(n):
  for j in range(i):
   if v[i]%v[j]==0:adj[i]|=1<<j;adj[j]|=1<<i
 diam=0;witness=None
 for i in range(n):
  seen=front=1<<i;dist=0
  while front:
   nxt=0;temp=front
   while temp:
    bit=temp&-temp;temp-=bit;nxt|=adj[bit.bit_length()-1]
   nxt&=~seen
   if not nxt:break
   dist+=1;seen|=nxt;front=nxt
  if dist>diam:diam=dist;witness=(v[i],v[(front&-front).bit_length()-1])
 return {'vertices':n,'diameter':diam,'witness_class_sizes':witness}
out=[]
for n in range(3,int(sys.argv[1])+1):
 S=set();A=set();count=0
 for p in parts(n):
  count+=1;freq=collections.Counter(p);z=math.prod(k**c*math.factorial(c) for k,c in freq.items());size=math.factorial(n)//z;S.add(size)
  if (n-len(p))%2==0:A.add(size//2 if all(k%2 and c==1 for k,c in freq.items()) else size)
 S.discard(1);A.discard(1);row={'n':n,'partitions':count,'S':diameter(sorted(S)),'A':diameter(sorted(A))};out.append(row);print(row,flush=True);(D/'outputs/divisibility.json').write_text(json.dumps(out,indent=2)+'\n')
