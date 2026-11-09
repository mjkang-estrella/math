import math,json,time,sys
import sympy as S
out=[]
for m in range(int(sys.argv[1]) if len(sys.argv)>1 else 5, int(sys.argv[2])+1 if len(sys.argv)>2 else 17):
 start=time.time();N=(1<<m)-1;factors=list(S.factorint(N));found=[];tested=0
 def mul(a,b):
  r=0
  while b:
   if b&1:r^=a
   b>>=1;a<<=1
   if a>>m:a^=mod
  return r
 def power(a,b):
  r=1
  while b:
   if b&1:r=mul(r,a)
   a=mul(a,a);b>>=1
  return r
 for mod in range((1<<m)+1,1<<(m+1),2):
  if mod.bit_count()%2==0:continue
  if power(2,N)!=1 or any(power(2,N//p)==1 for p in factors):continue
  tested+=1;h=[1]
  for z in range(m):
   roots=[N^(1<<z)]+[N^(1<<z)^(1<<w) for w in range(z)]
   for e in roots:
    a=power(2,e);hh=[0]*(len(h)+1)
    for j,b in enumerate(h):hh[j]^=mul(a,b);hh[j+1]^=b
    h=hh
  assert all(x in (0,1) for x in h)
  hb=sum(x<<i for i,x in enumerate(h));dividend=(1<<N)|1;g=0
  while dividend.bit_length()>=hb.bit_length():
   s=dividend.bit_length()-hb.bit_length();g|=1<<s;dividend^=hb<<s
  assert dividend==0
  wt=g.bit_count();found.append(dict(modulus=mod,h=hb,weight=wt,degree=g.bit_length()-1))
  if wt>1<<(m-2):break
  if tested>=20:break
 row=dict(m=m,primitive_moduli_tested=tested,trials=found,threshold=1<<(m-2),wall=time.time()-start);out.append(row);print(row,flush=True)
 json.dump(out,open('outputs/rm'+('-'+sys.argv[1] if len(sys.argv)>1 else '')+'.json','w'),indent=2)
