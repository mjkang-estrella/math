import pathlib,itertools,json,sys,collections,math
D=pathlib.Path(__file__).resolve().parents[1]
def iso(a,b):
 n=len(a);da=[v.bit_count() for v in a];db=[v.bit_count() for v in b]
 cand=[[j for j in range(n) if da[i]==db[j]] for i in range(n)];mapping={};used=set()
 order=sorted(range(n),key=lambda i:(len(cand[i]),-da[i]))
 def rec(k):
  if k==n:return True
  i=order[k]
  for j in cand[i]:
   if j in used or any(((a[i]>>x)&1)!=((b[j]>>y)&1) for x,y in mapping.items()):continue
   mapping[i]=j;used.add(j)
   if rec(k+1):return True
   used.remove(j);del mapping[i]
  return False
 return rec(0)
out=[]
for n in range(3,int(sys.argv[1])+1):
 pairs=list(itertools.combinations(range(n),2));masks={};av=set()
 for p in itertools.permutations(range(n)):
  pre=[];lo=n
  for a in p:pre.append(lo);lo=min(lo,a)
  mask=sum(1<<k for k,(i,j) in enumerate(pairs) if pre[i]<min(p[i],p[j]));masks.setdefault(mask,p)
  low=n;second=n;avoids=True
  for a in p:
   if a>second:avoids=False;break
   if a>low:second=min(second,a)
   low=min(low,a)
  if avoids:av.add(mask)
 def graph(m):
  a=[0]*n
  for k,(i,j) in enumerate(pairs):
   if m>>k&1:a[i]|=1<<j;a[j]|=1<<i
  return a
 key=lambda g:tuple(sorted(v.bit_count() for v in g))
 buckets=collections.defaultdict(list);count=0;clawfree=0;bad=[]
 for m in av:
  g=graph(m);k=key(g)
  if not any(iso(g,h) for h in buckets[k]):buckets[k].append(g);count+=1
 for m,p in masks.items():
  g=graph(m)
  if any(all(not(g[a]>>b&1) for a,b in itertools.combinations(t,2)) for v in range(n) for t in itertools.combinations([j for j in range(n) if g[v]>>j&1],3)):continue
  clawfree+=1
  if not any(iso(g,h) for h in buckets[key(g)]):bad.append({'permutation':p,'adjacency_bits':g})
 row={'n':n,'permutations':math.factorial(n),'distinct_labelled_graphs':len(masks),'avoiding_isomorphism_types':count,'clawfree_labelled_graphs':clawfree,'unmatched':bad};out.append(row);print(row,flush=True);(D/'outputs/competition-plain.json').write_text(json.dumps(out,indent=2)+'\n')
