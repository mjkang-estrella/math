"""Small exact F2 diagnostic; not a mathematical gate or classification proof."""
import itertools,json,signal
from pathlib import Path
signal.alarm(30)
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r124')
def rank(rows):
 piv={}
 for a in rows:
  while a:
   k=a.bit_length()-1
   if k not in piv:piv[k]=a;break
   a^=piv[k]
 return len(piv)
def calc(name,els,mul):
 n=len(els);idx={x:i for i,x in enumerate(els)};t=[[idx[mul(x,y)] for y in els] for x in els]
 assert all(t[0][i]==i and t[i][0]==i for i in range(n))
 assert all(t[t[a][b]][c]==t[a][t[b][c]] for a,b,c in itertools.product(range(n),repeat=3))
 pairs={(a,b):i for i,(a,b) in enumerate(itertools.product(range(1,n),repeat=2))}
 def term(a,b):return (1<<pairs[a,b]) if a and b else 0
 coc=[term(b,c)^term(t[a][b],c)^term(a,t[b][c])^term(a,b) for a,b,c in itertools.product(range(n),repeat=3)]
 cyc=[];orders=[]
 for g in range(1,n):
  p=0;row=0;d=0
  while True:
   row^=term(p,g);p=t[p][g];d+=1
   if p==0:break
   assert d<=n
  orders.append(d)
  if d%2==0:cyc.append(row)
 boundaries=[]
 for h in range(1,n):
  row=0
  for (a,b),i in pairs.items():
   if ((a==h)+(b==h)+(t[a][b]==h))%2:row|=1<<i
  boundaries.append(row)
 br=rank(boundaries);cr=rank(coc);kr=rank(coc+cyc)
 return {'group':name,'order':n,'variables':len(pairs),'cocycle_constraint_rank':cr,'boundary_rank':br,'H2_dimension':len(pairs)-cr-br,'cyclic_kernel_dimension':len(pairs)-kr-br,'nonidentity_orders':orders}
res=[]
for n in [2,3,4,6,8]:res.append(calc('C'+str(n),list(range(n)),lambda a,b:(a+b)%n))
res.append(calc('C2xC2',list(range(4)),lambda a,b:a^b))
# Q8 represented sign times 1,i,j,k, indexed sign*4+unit.
qtable=[[(0,0),(0,1),(0,2),(0,3)],[(0,1),(1,0),(0,3),(1,2)],[(0,2),(1,3),(1,0),(0,1)],[(0,3),(0,2),(1,1),(1,0)]]
def qmul(a,b):
 s,u=qtable[a%4][b%4];return 4*((a//4+b//4+s)%2)+u
res.append(calc('Q8',list(range(8)),qmul))
els=list(itertools.product(range(4),range(2)))
res.append(calc('D8',els,lambda x,y:((x[0]+(-1)**x[1]*y[0])%4,(x[1]+y[1])%2)))
(R/'notes/finite-diagnostic.json').write_text(json.dumps(res,indent=2))
for x in res:print(x['group'],'H2=',x['H2_dimension'],'cyclic kernel=',x['cyclic_kernel_dimension'])
