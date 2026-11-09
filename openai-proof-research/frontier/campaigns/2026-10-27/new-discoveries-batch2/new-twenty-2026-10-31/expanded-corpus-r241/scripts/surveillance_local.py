from pathlib import Path
import sys,random
D=Path(__file__).resolve().parents[1];rng=random.Random(2412)
def hit(x,t):
 n=len(x)+2;v=[0]*n;v[0]=1
 for _ in range(t):
  w=[0]*n;w[1]+=64*v[0]
  for i,a in enumerate(x,1):w[i+1]+=a*v[i];w[i-1]+=(64-a)*v[i]
  w[-1]+=64*v[-1];v=w
 return v[-1]
for n in [8,10,12,16,20,30,40]:
 count=0;best=0
 for t in range(n-1,2*n-2,2):
  base=hit([32]*(n-2),t)
  for j in range(250):
   half=[rng.randrange(-4,5) for _ in range((n-2)//2)];x=[32+a for a in half]+[32-a for a in half[::-1]]
   v=hit(x,t);count+=1
   if v>base:best+=1;print('BETTER',n,t,x,v,base,flush=True)
 print('ROW',n,count,'improvements',best,flush=True)
