import os,resource,itertools,json,time
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.time();out=[]
# Exhaustive normalized x-direction derivative. Every APN map must have kernel size 2 in every direction.
for m,mod in [(4,0b10011),(5,0b100101),(6,0b1000011),(7,0b10000011),(8,0b100011101)]:
 q=1<<m
 def mul(a,b):
  r=0
  while b:
   if b&1:r^=a
   b>>=1;a<<=1
   if a&q:a^=mod
  return r
 table=[[mul(a,b)for b in range(q)]for a in range(q)];sq=[table[a][a]for a in range(q)];cube=[table[a][sq[a]]for a in range(q)]
 for u in range(q):
  # direction (1,0,0): derivative equations x^2+x+1, u*z^2, u*y
  # If u nonzero kernel two => use directions (1,b,c) searching for >2 zero derivative homogeneous part.
  found=None
  for b,c in itertools.product(range(min(q,8)),repeat=2):
   basis=[]
   def B(x,y,z):return ((sq[x]^x^table[u][table[sq[b]][z]^table[y][0]]) | 0)
   # quadratic polar D_a C: x²*a+x*a² + u*(b²*z+y²*c), cyclic
   aa=(1,b,c)
   cols=[]
   for k in range(3*m):
    xx=[0,0,0];xx[k//m]=1<<(k%m);yy=[]
    for i in range(3):
     a0,a1,a2=aa[i],aa[(i+1)%3],aa[(i+2)%3];x0,x1,x2=xx[i],xx[(i+1)%3],xx[(i+2)%3]
     yy.append(table[sq[x0]][a0]^table[x0][sq[a0]]^table[u][table[sq[a1]][x2]^table[sq[x1]][a2]])
    cols.append(sum(v<<(m*i)for i,v in enumerate(yy)))
   piv={}
   for v in cols:
    while v:
     k=v.bit_length()-1
     if k in piv:v^=piv[k]
     else:piv[k]=v;break
   nullity=3*m-len(piv)
   if nullity>=2:found={'direction':aa,'kernel_size':1<<nullity};break
  out.append({'m':m,'modulus_bits':mod,'u':u,'non_apn_witness':found})
  json.dump({'coverage':out,'seconds':time.time()-start},open('outputs/apn.json','w'),indent=2)
  if time.time()-start>100:raise SystemExit
print('checked',len(out))
