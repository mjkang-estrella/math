import random,math,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];random.seed(105)
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def calc(adj,u=0,p=-1):
 a=[0,1];b=[1];sel=1;un=0;dom=0;delta=10000;children=0
 for v in adj[u]:
  if v==p:continue
  children+=1;aa,bb,s,d,r=calc(adj,v,u);a=mul(a,bb);b=mul(b,add(aa,bb));sel+=min(d,r);un+=d;dom+=min(s,d);delta=min(delta,s-min(s,d))
 if not children:dom=10000
 else:dom+=delta
 return a,b,sel,dom,un
out=[]
for n in [4,5,6,8,12,13,16,20,30,50,80]:
 worst=-100;w=None
 for trial in range(1000):
  adj=[[] for _ in range(n)]
  for v in range(1,n):
   # random recursive tree, path biased, star biased
   p=random.randrange(v) if trial%3==0 else max(0,v-1-random.randrange(min(v,3))) if trial%3==1 else random.randrange(min(v,4))
   adj[p].append(v);adj[v].append(p)
  a,b,s,d,_=calc(adj);pol=add(a,b);M=0
  while sum(x*(-1)**i for i,x in enumerate(pol))==0:
   # synthetic division by x+1 ascending
   q=[0]*(len(pol)-1);q[-1]=pol[-1]
   for i in range(len(q)-2,-1,-1):q[i]=pol[i+1]-q[i+1]
   pol=q;M+=1
  ind=min(s,d);gap=abs(M-ind+1);bound=(n+1)//2-2
  if gap-bound>worst:worst=gap-bound;w=dict(independent_domination=ind,M=M,gap=gap,bound=bound,edges=[[u,v]for u in range(n)for v in adj[u]if u<v])
 z=dict(n=n,trees=1000,max_gap_minus_bound=worst,witness=w);out.append(z);print(n,worst,flush=True);(D/'outputs/tree-band.json').write_text(json.dumps(out,indent=2))
