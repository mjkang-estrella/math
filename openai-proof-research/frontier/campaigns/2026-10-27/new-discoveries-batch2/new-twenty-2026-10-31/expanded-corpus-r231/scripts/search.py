import pathlib,json,itertools,random,sys,time
D=pathlib.Path(__file__).resolve().parents[1];random.seed(231)
def pinnable():
 out=[]
 for n,p,r,s,trials in [(10,5,3,3,3000),(12,6,3,3,3000),(14,7,3,3,2000),(12,6,3,4,2000),(14,7,4,4,1000)]:
  def edges(k):return [sum(1<<v for v in (i,)+tail) for i in range(p) for tail in itertools.combinations(range(p,n),k-1)]
  E,F=edges(r),edges(s); full=(1<<n)-1; tested=0;support=0;hist={};bad=None
  covers=[sum(1<<v for v in t) for t in itertools.combinations(range(n),r+s-2)]
  for _ in range(trials):
   A=random.sample(E,random.randint(1,min(len(E),2*n)))
   B=[f for f in F if all(f&e for e in A)]
   if not B:continue
   A=[e for e in E if all(e&f for f in B)]
   if __import__('functools').reduce(int.__or__,A,0)!=full or __import__('functools').reduce(int.__or__,B,0)!=full:continue
   support+=1;H=A+B;tested+=1
   c=next((c for c in covers if all(c&e for e in H)),None)
   if c is None:bad={'A':A,'B':B};break
  result=dict(n=n,pin_size=p,r=r,s=s,trials=trials,valid_same_support_closed_pairs=tested,counterexample=bad)
  print(result,flush=True);out.append(result)
 (D/'pinnable-search.json').write_text(json.dumps(out,indent=2)+'\n')
def ordering():
 out=[]
 for dims,mod,trials in [(1,29,2000),(1,31,2000),(1,41,2000),(3,3,2000),(4,3,2000),(2,5,2000),(2,7,2000)]:
  G=list(itertools.product(range(mod),repeat=dims));zero=(0,)*dims
  neg=lambda x:tuple(-v%mod for v in x)
  add=lambda x,y:tuple((v+w)%mod for v,w in zip(x,y))
  counts={};valid=0;nodes=0;bad=None
  for it in range(trials):
   reps=[x for x in G if x<neg(x)];random.shuffle(reps); k=random.randint(3,min(22,len(reps)))
   X=[random.choice([x,neg(x)]) for x in reps[:k-1]];z=zero
   for x in X:z=add(z,x)
   z=neg(z)
   if z==zero or z in X or neg(z) in X or z==neg(z):continue
   X.append(z);valid+=1
   def dfs(rem,z,seen):
    nonlocal nodes
    nodes+=1
    if len(rem)==1:return True
    for x in rem:
     w=add(z,x)
     if w not in seen and dfs([y for y in rem if y!=x],w,seen|{w}):return True
    return False
   # cyclic rotation symmetry fixes first member
   ok=dfs(X[1:],X[0],{zero,X[0]});counts[str(k)]=counts.get(str(k),0)+1
   if not ok:bad=X;break
  res=dict(group='C'+str(mod)+'^'+str(dims),draws=trials,valid_zero_sum_inverse_free_sets=valid,size_counts=counts,dfs_nodes=nodes,counterexample=bad)
  print(res,flush=True);out.append(res)
 (D/'ordering-search.json').write_text(json.dumps(out,indent=2)+'\n')
if sys.argv[1]=='pinnable':pinnable()
else:ordering()
