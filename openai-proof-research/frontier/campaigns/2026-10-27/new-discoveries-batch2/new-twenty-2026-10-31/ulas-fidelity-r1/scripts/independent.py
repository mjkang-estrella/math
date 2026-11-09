from pathlib import Path
import json,re
L=Path(__file__).resolve().parent.parent
N=256
rows=[]
def v2(a):
 assert a
 a=abs(a);return (a&-a).bit_length()-1
for m in [1,2,3,4,5,6,7,8,9,11,15,19,23,27,31]:
 a=[1]+[0]*N
 # Multiply one geometric series per colour, directly from the defining product.
 s=1
 while s<=N:
  for colour in range(2*m if s==1 else m):
   for n in range(s,N+1):a[n]+=a[n-s]
  s*=2
 for n in range(1,N//4+1):
  d=a[4*n]-a[n];v=v2(d)
  if m%2==0:assert v==v2(n)+2*v2(m//2)+3
  elif m%4==1:
   assert v>=v2(n)+3
   if n%2:assert v==v2(n)+3
  else:
   assert v>=v2(n)+6
   if m%16 in [3,7] and n%2 or m%16==11 and n%4==2:assert v==v2(n)+6
   if m%16==15:assert v>=v2(n)+7 and v!=v2(n)+6
  if n in [1,2,3,6]:rows.append(dict(m=m,n=n,c_n=a[n],c_4n=a[4*n],diff=d,val=v))
 assert a[1]==2*m
 if m==15:assert a[4]==48030
print(json.dumps(dict(pairs=15*64,rows=rows,all_checks=True),indent=2))
