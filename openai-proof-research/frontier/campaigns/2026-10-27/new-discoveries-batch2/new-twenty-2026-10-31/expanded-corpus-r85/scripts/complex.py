import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def rank(cols):
 piv={}
 for c in cols:
  while c:
   j=c.bit_length()-1
   if j in piv:c^=piv[j]
   else:piv[j]=c;break
 return len(piv)
def cm(K):
 d=max(x.bit_count() for x in K)
 for f in K:
  L={x for x in K if not x&f and x|f in K};r=max(x.bit_count() for x in L)
  if r!=d-f.bit_count():return False
  by=[[x for x in L if x.bit_count()==k] for k in range(r+1)]
  ranks=[0]
  for k in range(1,r+1):
   ix={x:i for i,x in enumerate(by[k-1])}
   cols=[sum(1<<ix[x^(1<<j)] for j in range(x.bit_length()) if x>>j&1) for x in by[k]]
   ranks.append(rank(cols))
  for k in range(r):
   if len(by[k])-ranks[k]-ranks[k+1]:return False
 return True
def fv(K):return tuple(sum(x.bit_count()==k for x in K) for k in range(max(x.bit_count() for x in K)+1))
def balanced(K,n):
 d=len(fv(K))-1
 return any(all(all(c[i]!=c[j] for i in range(n) for j in range(i) if (1<<i|1<<j) in K) for _ in [0]) for c in itertools.product(range(d),repeat=n))
if __name__ == "__main__":
 res=[]
 for n in range(1,6):
  nontriv=sorted([x for x in range(1<<n) if x.bit_count()>1],key=lambda x:(x.bit_count(),x));K={0}|{1<<i for i in range(n)};vectors=set();total=0
  def walk(j):
   global total
   if j==len(nontriv):
    total+=1
    if cm(K) and balanced(K,n):vectors.add(fv(K))
    return
   x=nontriv[j];walk(j+1)
   if all(x^(1<<i) in K for i in range(n) if x>>i&1):
    K.add(x);walk(j+1);K.remove(x)
  walk(0)
  edges=list(itertools.combinations(range(n),2));checked=0;cmcount=0;bad=[]
  for bits in range(1<<len(edges)):
   E={1<<a|1<<b for j,(a,b) in enumerate(edges) if bits>>j&1};L={x for x in range(1<<n) if all((1<<a|1<<b) in E for a,b in itertools.combinations([i for i in range(n) if x>>i&1],2))};checked+=1
   if cm(L):
    cmcount+=1
    if fv(L) not in vectors:bad.append(bits)
  res.append(dict(n=n,all_complexes_on_exact_vertices=total,balanced_CM_fvectors=len(vectors),graphs=checked,flag_CM_over_F2=cmcount,no_witness_on_same_vertices=bad));print(res[-1],flush=True)
 (D/'outputs/340460-search.json').write_text(json.dumps(dict(results=res,method='Reisner criterion via reduced link homology over F2; exact bit Gaussian elimination; enumerate all downward complexes and all colorings for balanced witnesses',limitation='F2 only; not a proof for other characteristic or arbitrary n'),indent=2)+'\n')
