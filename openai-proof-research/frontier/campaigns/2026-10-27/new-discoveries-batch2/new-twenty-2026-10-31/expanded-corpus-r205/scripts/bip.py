import itertools,random,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(205)
perms=list(itertools.permutations(range(3)))
def trans(mask,p,q):return sum(1<<(p[i]*3+q[j]) for i in range(3) for j in range(3) if mask>>(i*3+j)&1)
trees=[];seen=set()
for es in itertools.combinations(range(9),5):
 mask=sum(1<<e for e in es)
 if mask in seen:continue
 reach={0}
 while True:
  nxt=reach|{3+j for i in reach if i<3 for j in range(3) if mask>>(3*i+j)&1}|{i for j in reach if j>=3 for i in range(3) if mask>>(3*i+j-3)&1}
  if nxt==reach:break
  reach=nxt
 if len(reach)<6:continue
 iso={trans(mask,p,q) for p in perms for q in perms};seen|=iso;trees.append(sorted(iso))
out=[]
for n in [6,7,8]:
 bound=2*(2*n-4);subsets=list(itertools.combinations(range(n),3));bad=[]
 for trial in range(1500):
  edges=set(rng.sample(range(n*n),bound+1));found=[False]*len(trees)
  for a in subsets:
   for b in subsets:
    sub=sum(1<<(i*3+j) for i in range(3) for j in range(3) if a[i]*n+b[j] in edges)
    for z,ts in enumerate(trees):
     if not found[z] and any(sub&t==t for t in ts):found[z]=True
    if all(found):break
   if all(found):break
  if not all(found):bad.append({'edges':sorted(edges),'missing':found});break
 r={'n':n,'m':n,'k':3,'l':3,'edges':bound+1,'random_seed':205,'graphs_checked':trial+1,'ordered_bipartite_tree_types':len(trees),'bad':bad};out.append(r);print(json.dumps(r),flush=True)
(D/'outputs/bip.json').write_text(json.dumps(out,indent=2))
