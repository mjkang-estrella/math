from pathlib import Path
import itertools,json
def weight(n,i,j):return int(i+j//2<=n)+int(j+i//2<=n)+int(2*(j-i)<=n)+int(2*(j-i)+1<=n)+1+int(i-j//2>=1)
def count(c):
 n=len(c)-1
 return sum(c[x]==c[y]==c[x+y//2] for y in range(1,n+1) for x in range(1,n-y//2+1))
def source(n):return [None]+[int((n+3)//6<i<=(n+1)//2 or i>(5*n+3)//6) for i in range(1,n+1)]
L=Path(__file__).resolve().parent
out=[]
for n in (12,13):
 W=[[0]*(n+1) for _ in range(n+1)]
 for i in range(1,n+1):
  for j in range(i+1,n+1):W[i][j]=W[j][i]=weight(n,i,j)
 trapped=[];tested=0
 for bits in itertools.product(range(2),repeat=n-1):
  c=[None,0]+list(bits);m=count(c);tested+=1
  if m<=(n*n+5)//6:continue
  s=[0]+[1-2*v for v in c[1:]]
  fields=[0]+[sum(W[i][j]*s[i]*s[j] for j in range(1,n+1)) for i in range(1,n+1)]
  gains=[]
  for a in range(1,n+1):
   boundary=0
   for b in range(a,n+1):
    boundary+=fields[b]-2*sum(W[i][b]*s[i]*s[b] for i in range(a,b))
    assert boundary%2==0
    gains.append((-boundary//2,a,b))
  if min(gains)[0]>=0:
   d=source(n);F=[i for i in range(1,n+1) if c[i]!=d[i]]
   ss=set(F);delta=-sum(W[i][j]*s[i]*s[j] for i in ss for j in range(1,n+1) if j not in ss)//2
   assert delta==count(d)-m
   trapped.append(dict(c=c[1:],M=m,min_interval_delta=min(gains),zero_intervals=[[a,b] for delta,a,b in gains if delta==0],source_flip_set=F,source_delta=delta))
 out.append(dict(n=n,tested=tested,trap_count=len(trapped),first_traps=trapped[:3]))
(L/'interval-exchange.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
