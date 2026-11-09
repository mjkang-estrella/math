import pathlib,json,itertools,functools,sys,collections
D=pathlib.Path(__file__).resolve().parents[1]
def add(d,k,v):
 d[k]+=v
 if d[k]==0:del d[k]
@functools.lru_cache(None)
def power(n):
 if n==0:return {():1}
 out=collections.defaultdict(int);out[(n,)]=(-1)**(n-1)*n
 for i in range(1,n):
  for p,c in power(n-i).items():add(out,tuple(sorted(p+(i,))),(-1)**(i-1)*c)
 return dict(out)
def mul(a,b):
 out=collections.defaultdict(int)
 for x,c in a.items():
  for y,d in b.items():add(out,tuple(sorted(x+y)),c*d)
 return dict(out)
@functools.lru_cache(None)
def convert(parts,r):
 out={():1}
 for s in parts:out=mul(out,power(s))
 pointed={(p,1):c for p,c in out.items()}
 for _ in range(r):
  nxt=collections.defaultdict(int)
  for (p,i),c in pointed.items():
   add(nxt,(tuple(sorted(p+(i,))),1),c)
   add(nxt,(p,i+1),-c)
  pointed=dict(nxt)
 return pointed
def check(m):
 n=len(m);state={tuple(1<<i for i in range(n)):1}
 for u in range(n):
  for v in range(u+1,m[u]):
   nxt=collections.defaultdict(int,state)
   for p,c in state.items():
    a=next(t for t in p if t>>u&1);b=next(t for t in p if t>>v&1)
    q=p if a==b else tuple(sorted([t for t in p if t!=a and t!=b]+[a|b]))
    add(nxt,q,-c)
   state=dict(nxt)
 raw=collections.defaultdict(int)
 for p,c in state.items():
  root=next(t for t in p if t&1);add(raw,(tuple(sorted(t.bit_count() for t in p if t!=root)),root.bit_count()-1),c)
 out=collections.defaultdict(int)
 for (p,r),c in raw.items():
  for key,d in convert(p,r).items():add(out,key,c*d)
 return dict(out)
rows=[]
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 count=0;connected=0
 for m in itertools.combinations_with_replacement(range(1,n+1),n):
  if any(m[i]<i+1 for i in range(n)):continue
  count+=1
  if len(sys.argv)>3 and m[0]!=int(sys.argv[3]):continue
  if any(m[i]==i+1 for i in range(n-1)):continue
  connected+=1;out=check(m)
  if any(c<0 for c in out.values()):
   print('NEGATIVE',m,out,flush=True);raise SystemExit
 rows.append({'n':n,'all_hessenberg_functions':count,'connected_checked':connected});print(rows[-1],flush=True)
 (D/f'pointed-progress-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(rows,indent=2))
(D/f'pointed-results-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(rows,indent=2))
