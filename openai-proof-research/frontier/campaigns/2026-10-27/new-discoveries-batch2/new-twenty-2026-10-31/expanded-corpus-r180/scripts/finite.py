import itertools as it,random,json,pathlib,sys,math,time
D=pathlib.Path(__file__).resolve().parents[1]; rng=random.Random(180)
def quasi(a,n):
 incoming=[sum((1<<u) for u in range(n) if a[u]>>v&1) for v in range(n)]
 margins=[x.bit_count()-sum(1 for v in range(n) if not ((x|1<<u)>>v&1) and incoming[v] and not incoming[v]&~(x|1<<u)) for u,x in enumerate(a) if x]
 return max(margins) if margins else None

def run_quasi():
 out=[]
 for n in range(2,6):
  pairs=list(it.combinations(range(n),2));worst=n;count=0
  for code in it.product(range(3),repeat=len(pairs)):
   if not any(code):continue
   a=[0]*n
   for (u,v),t in zip(pairs,code):
    if t==1:a[u]|=1<<v
    if t==2:a[v]|=1<<u
   q=quasi(a,n);worst=min(worst,q);count+=1
   if q<0: print('COUNTEREXAMPLE',a,flush=True);return
  out.append(dict(kind='all labelled oriented nonempty arc graphs',n=n,count=count,min_best_margin=worst));print(out[-1],flush=True)
 for n in range(2,5):
  pairs=[(u,v) for u in range(n) for v in range(n) if u!=v];count=0
  for code in range(1,1<<len(pairs)):
   a=[0]*n
   for k,(u,v) in enumerate(pairs):
    if code>>k&1:a[u]|=1<<v
   if quasi(a,n)<0:print('COUNTEREXAMPLE',a,flush=True);return
   count+=1
  out.append(dict(kind='all labelled loopless digraphs with arcs; digons allowed',n=n,count=count));print(out[-1],flush=True)
 for n in [6,8,12,20,40]:
  worst=n
  for t in range(2000):
   d=rng.randint(1,min(10,n-1));a=[sum(1<<v for v in rng.sample([v for v in range(n) if v!=u],d)) for u in range(n)]
   q=quasi(a,n);worst=min(worst,q)
   if q<0: print('COUNTEREXAMPLE',a,flush=True);return
  out.append(dict(kind='random fixed outdegree loopless digraph',n=n,count=2000,min_best_margin=worst));print(out[-1],flush=True)
 (D/'outputs/quasi.json').write_text(json.dumps(out,indent=2))
def per(a):
 return sum(math.prod(a[i][p[i]] for i in range(len(a))) for p in it.permutations(range(len(a))))
def expok(cols,m):
 return all(sum(any(c[i] for i in range(m) if mask>>i&1) for c in cols)>=2*mask.bit_count()-1 for mask in range(1,1<<m))
def failure(cols,m):
 return all(per([[cols[j][i] for j in sub] for i in range(m)])==0 for sub in it.combinations(range(len(cols)),m))
def run_per():
 out=[]
 for m,n in [(2,3),(3,5)]:
  types=[c for c in it.product([-1,0,1],repeat=m) if any(c) and next(x for x in c if x)!=-1];count=eligible=0
  for cols in it.combinations_with_replacement(types,n):
   count+=1
   if not expok(cols,m):continue
   eligible+=1
   if failure(cols,m):print('COUNTEREXAMPLE',cols,flush=True);return
  out.append(dict(m=m,n=n,canonical_ternary_matrices=count,expansion_eligible=eligible,counterexamples=0));print(out[-1],flush=True)
 m,n=4,7;types=[c for c in it.product([-1,0,1],repeat=m) if any(c) and next(x for x in c if x)!=-1];eligible=0
 for t in range(30000):
  cols=[rng.choice(types) for j in range(n)]
  if not expok(cols,m):continue
  eligible+=1
  if failure(cols,m):print('COUNTEREXAMPLE',cols,flush=True);return
 out.append(dict(m=m,n=n,random_ternary_matrices=30000,expansion_eligible=eligible,counterexamples=0));print(out[-1],flush=True)
 (D/'outputs/permanent.json').write_text(json.dumps(out,indent=2))
if sys.argv[1]=='quasi':run_quasi()
if sys.argv[1]=='permanent':run_per()
