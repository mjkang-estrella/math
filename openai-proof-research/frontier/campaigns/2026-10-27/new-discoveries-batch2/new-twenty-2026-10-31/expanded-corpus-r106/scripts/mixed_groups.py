import random,json
rng=random.Random(106363220)
def sylow(n):
 if n==1:return [(0,)]
 m=n//2;P=sylow(m);out=[]
 for a in P:
  for b in P:
   out.append(a+tuple(x+m for x in b));out.append(tuple(x+m for x in a)+b)
 return out
def sylown(n):
 out=[()];offset=0
 for k in range(n.bit_length()-1,-1,-1):
  m=1<<k
  if n&m:out=[a+tuple(x+offset for x in b) for a in out for b in sylow(m)];offset+=m
 return out
out=[]
for n in range(13,17):
 H=sylown(n);H=[p for p in H if p!=tuple(range(n))];base=[j//4 for j in range(n)];success=None;intersection_sizes=[]
 for trial in range(1000):
  colors=base.copy();rng.shuffle(colors);count=1
  for p in H:
   mapping={};ok=True
   for i in range(n):
    a,b=colors[i],colors[p[i]]
    if a in mapping and mapping[a]!=b:ok=False;break
    mapping[a]=b
   if ok:count+=1
  intersection_sizes.append(count)
  if count==1:success=colors;break
 out.append({'n':n,'H_order':len(H)+1,'K':'S4 wreath S_floor(n/4) times S_(n mod4), natural blocks','partitions_sampled':len(intersection_sizes),'minimum_intersection_order':min(intersection_sizes),'regular_witness_block_labels':success});print(out[-1],flush=True);open('outputs/mixed-groups.json','w').write(json.dumps(out,indent=2))
