import itertools,json,pathlib
from collections import Counter
P=pathlib.Path(__file__).resolve().parent
# Independently test whole trial stack in top-to-bottom order.
def bad(s):
 return any(s[i]<s[j]<s[j+1] for i in range(len(s)) for j in range(i+1,len(s)-1))
def sc(p):
 s=[];o=[]
 for x in p:
  while bad([x]+s):o.append(s.pop(0))
  s.insert(0,x)
 return tuple(o+s)
assert sc((5,1,4,3,6,2))==(6,3,2,4,1,5)
c=Counter();fib={}
for p in itertools.permutations(range(1,6)):
 o=sc(p);c[o]+=1;fib.setdefault(o,[]).append(p)
w=[{'output':o,'preimages':fib[o]} for o,v in c.items() if v==5]
# A non-named output with at least as many preimages as the named output.
a=(6,5,4,3,2,8,1,7);named=(7,6,5,4,3,2,1,8);fa=[];fn=[]
for p in itertools.permutations(range(1,9)):
 o=sc(p)
 if o==a:fa.append(p)
 if o==named:fn.append(p)
assert len(fa)==len(fn)==64
edges=list(itertools.combinations(range(4),2));bw=None
for order in itertools.permutations(edges):
 d=[[0]*4 for _ in range(4)]
 for rank,(x,y) in enumerate(order,1):d[x][y]=d[y][x]=rank
 balls=set()
 for c0 in range(4):
  for radius in range(7):balls.add(tuple(x for x in range(4) if d[c0][x]<=radius))
 if len(balls)==9:bw={'distance_rank_matrix':d,'balls':sorted(balls),'count':len(balls)};break
assert bw and len(set(d[x][y] for x,y in edges))==6
result={'stack_source_example_PASS':True,'stack_n5_second5_outputs':w,'stack_n8_tie':{'alternative':a,'named':named,'alternative_fiber':fa,'named_fiber':fn},'ball_n4':bw,'proof_limit':'Exact finite certificates; not Lean, not prior-art clearance.'}
(P/'witnesses.json').write_text(json.dumps(result,indent=2)+'\n')
print('n5:',w);print('n8 fibers:',len(fa),len(fn));print('ball:',bw)
