import math,json,time
start=time.time();bound=128;amax=199;N=amax*bound+amax
# Euler's pentagonal recurrence, mod 2
p=[0]*(N+1);p[0]=1;pent=[]
for k in range(1,math.isqrt(2*N)+1):
 for x in [k*(3*k-1)//2,k*(3*k+1)//2]:
  if x<=N:pent.append(x)
pent.sort()
for n in range(1,N+1):
 v=0
 for g in pent:
  if g>n:break
  v^=p[n-g]
 p[n]=v

def invpower(d,r):
 v=[0]*(bound+1);v[0]=1;b=0
 while r:
  if r&1:
   step=d*(1<<b)
   for q in range(step,bound+1,step):
    for j in range(q,bound+1):v[j]^=v[j-q]
  r>>=1;b+=1
 return sum(x<<i for i,x in enumerate(v))
rows=[]
for a in range(5,amax+1,2):
 if a%3==0:continue
 k=(a*a-1+24*a-1)//(24*a);b=pow(24,-1,a)
 target=sum(p[a*(n-k)+b]<<n for n in range(k,bound+1))
 cols=[];labels=[]
 for d in range(1,a+1):
  if a%d:continue
  for j in range(k//d+1):
   r=a//d-24*j
   if r<0:continue
   cols.append((invpower(d,r)<<(d*j))&((1<<(bound+1))-1));labels.append([d,j])
 target^=cols[0];basis={}
 for idx,c in enumerate(cols[1:],1):
  mask=1<<idx
  while c:
   pivot=c.bit_length()-1
   if pivot in basis:c^=basis[pivot][0];mask^=basis[pivot][1]
   else:basis[pivot]=(c,mask);break
 sol=1
 while target:
  pivot=target.bit_length()-1
  if pivot not in basis:break
  v,mask=basis[pivot];target^=v;sol^=mask
 rows.append({'a':a,'t':1,'b':b,'k':k,'q_through':bound,'consistent':target==0,'chosen_terms':[labels[i] for i in range(len(cols)) if sol>>i&1] if not target else []})
print(json.dumps({'rows':rows,'seconds':time.time()-start}))
