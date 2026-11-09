import pathlib,json,itertools,random,sys,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(190)
def template(n,p):
 ix={(a,b):j for j,(a,b) in enumerate(itertools.combinations(range(1,n),2))};fs=[]
 for k in range(1,n-1,2):
  es=[]
  for j in [k,k+1]:es += [(n-1,j)]+[((j+z)%(n-1),(j-z)%(n-1)) for z in range(1,n//2)]
  adj=[[] for _ in range(n)]
  for a,b in es:adj[a].append(b);adj[b].append(a)
  seen=set()
  for a in range(n):
   if a in seen:continue
   prev=-1;v=a;mask=0
   while v not in seen:
    seen.add(v);w=next(z for z in adj[v] if z!=prev);e=tuple(sorted((p[v],p[w])))
    if e[0]:mask^=1<<ix[e]
    prev,v=v,w
   fs.append(mask)
 return tuple(sorted(fs))
n=int(sys.argv[1]);ts=set()
if n==8:
 for p in itertools.permutations(range(1,n)):ts.add(template(n,(0,)+p))
else:
 for _ in range(2000):ts.add(template(n,[0]+rng.sample(list(range(1,n)),n-1)))
ts=sorted(ts);bad=[];tested=0
masks=range(1<<21) if n==8 else [sum((rng.random()<pr)<<j for j in range((n-1)*(n-2)//2)) for pr in [.02,.1,.3,.5,.7,.9,.98] for _ in range(100)]
for m in masks:
 tested+=1
 for t in ts:
  if all((m&f).bit_count()%2==0 for f in t):break
 else:bad.append(m)
 if len(bad)>1000:break
out={'n':n,'tested':tested,'templates':len(ts),'uncovered_masks':bad,'meaning':'Each covered signature has a zero perfect matching plus balanced 2-factors, yielding an (n-1)-edge coloring. Uncovered is not an obstruction.'}
(D/f'outputs/signed-masks-{n}.json').write_text(json.dumps(out,indent=2));print(out)
