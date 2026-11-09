import itertools,json
for n in range(1,8):
 es=list(itertools.combinations(range(n),2));lo=n//3;hi=(n+2)//3;lab=[]
 for c in itertools.product(range(3),repeat=n):
  if c[0]!=0 or any(c.count(j)<lo or c.count(j)>hi for j in range(3)):continue
  # every permutation of Z3 is affine, inducing a permutation on edge sums
  seen=[]
  for x in c:
   if x not in seen:seen.append(x)
  if seen!=list(range(len(seen))):continue
  masks=[sum(1<<i for i,(u,v) in enumerate(es) if (c[u]+c[v])%3==j) for j in range(3)];lab.append(masks)
 count=0
 for g in range(1<<len(es)):
  ok=False
  for ms in lab:
   ns=[(g&m).bit_count() for m in ms]
   if max(ns)-min(ns)<=1:ok=True;break
  if not ok:print(json.dumps({'FAIL':True,'n':n,'mask':g}),flush=True);raise SystemExit()
  count+=1
 print(json.dumps({'n':n,'all_labeled_simple_graphs':count,'balanced_vertex_partitions_up_to_color_permutation':len(lab),'failures':0}),flush=True)
