import pathlib,json,sys,itertools,math,random
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];out=[]
def emit(x):
 out.append(x);print(x,flush=True);(D/'outputs'/f'{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
if mode=='permutations':
 import collections
 pats=[[(2,1,3,4),(4,2,1,5,3),(2,4,1,5,3)],[(2,1,4,3),(4,2,1,3,5),(2,4,1,3,5)]]
 cs=[[()],[()]]
 for n in range(1,10):
  counts=[]
  for cls in range(2):
   ns=[];ct=collections.Counter()
   for p in cs[cls]:
    for j in range(n):
     q=p[:j]+(n,)+p[j:];bad=False
     for pat in pats[cls]:
      k=len(pat);mx=pat.index(k)
      for ix in itertools.combinations([a for a in range(n) if a!=j],k-1):
       ids=sorted(ix+(j,))
       if ids[mx]!=j:continue
       vals=[q[a] for a in ids]
       if all((vals[a]<vals[b])==(pat[a]<pat[b]) for a in range(k) for b in range(a)):bad=True;break
      if bad:break
     if bad:continue
     ns.append(q);inv=[0]*n
     for a,v in enumerate(q):inv[v-1]=a
     d=sum(q[a]>q[a+1] for a in range(n-1));ii=sum(inv[a]>inv[a+1] for a in range(n-1))
     ct[(d,ii) if cls==0 else (n-1-d,n-1-ii)]+=1
   cs[cls]=ns;counts.append(ct)
  emit({'n':n,'sizes':list(map(len,cs)),'equal':counts[0]==counts[1],'distribution':[[list(k),v] for k,v in sorted(counts[0].items())]})
if mode=='digits-dual':
 import numpy as np
 from scipy.optimize import linprog
 from fractions import Fraction
 for p in [13,17,29,37,41,53,61,73,97,101]:
  ds=list(range((p+1)//2))+[(p+3)//2];ix={v:j for j,v in enumerate(ds)};aps=[[(a+k*b)%p for k in range(4)] for a in ds for b in range(1,p) if all((a+k*b)%p in ix for k in range(4))];A=np.zeros((len(aps),3*len(ds)))
  for j,ap in enumerate(aps):
   for k in range(1,4):A[j,(k-1)*len(ds)+ix[ap[k]]]+=1;A[j,(k-1)*len(ds)+ix[ap[0]]]-=1
  r=linprog(np.zeros(A.shape[1]),A_ub=-A,b_ub=-np.ones(len(aps)),bounds=(None,None),method='highs',options={'presolve':False})
  y=[Fraction(float(v)).limit_denominator(100000) for v in r.x] if r.success else []
  margins=[sum(Fraction(int(v))*z for v,z in zip(row,y)) for row in A] if y else []
  emit({'p':p,'status':r.status,'exact_separating_potential':bool(y) and min(margins)>=1,'potential':[[str(z) for z in y[k*len(ds):(k+1)*len(ds)]] for k in range(3)],'min_margin':str(min(margins)) if margins else None})
if mode=='schur':
 N=20000;a=[0]*(N+1);a[0]=1
 for d in range(1,N+1):
  if d%6 not in [0,1,5]:continue
  for j in range(d,N+1):a[j]=(a[j]+a[j-d])%32
 for b in [31,43,59,63]:
  ns=list(range((N-(4*b-1))//256+1));bad=[n for n in ns if a[256*n+4*b-1]!=a[64*n+b]]
  emit({'b':b,'n_range':[0,ns[-1]],'bad':bad,'largest_S_index':256*ns[-1]+4*b-1})
if mode=='codes':
 # Binary subfield complement: invertible trace coordinates identify ambient F_2^(nm). Every proper coordinate subspace D tested, all nonzero linear functionals.
 for N in range(2,10):
  for s in range(1,N):
   vals=[sum((x&v).bit_count()%2 for x in range(1<<s,1<<N)) for v in range(1,1<<N)]
   emit({'ambient_dimension':N,'subspace_dimension':s,'actual_weights':sorted(set(vals)),'predicted':[2**(N-1)-2**(s-1),2**(N-1)],'match':sorted(set(vals))==[2**(N-1)-2**(s-1),2**(N-1)]})
if mode=='cyclic':
 for v in range(2,17):
  checked=0;bad=[]
  for mask in range(1,1<<(v-1)):
   T=[j+1 for j in range(v-1) if mask>>j&1];total=sum(T)%v
   def go(left,s,seen):
    if not left:return True
    for x in left:
     t=(s+x)%v
     if t in seen:continue
     if go(left-{x},t,seen|{t}):return True
    return False
   # source distinct partial sums permits zero once; exclude initial zero only if total nonzero (Alspach stronger).
   if not go(set(T),0,set()):bad.append(T)
   checked+=1
  emit({'v':v,'nonempty_subsets':checked,'bad':bad,'source_distinct_partial_sums':True,'raw_nonzero_counterexample':[1,v-1] if v>2 else None})
if mode=='digraphs':
 for p in [2,3,5,7,11,13,17,19,23,29,31]:
  subgroups=set()
  for a in range(1,p):
   H={1};x=a
   while x!=1:H.add(x);x=x*a%p
   subgroups.add(tuple(sorted(H)))
  count=0
  for H in subgroups:
   seen=set()
   for a in range(1,p):
    S=tuple(sorted({a*h%p for h in H}))
    if S in seen:continue
    seen.add(S);count+=1
    # Adjacency AA^t=A^tA: count difference multiplicities exactly.
    c=[sum((s-t)%p==d for s in S for t in S) for d in range(p)]
    assert c==[c[-d%p] for d in range(p)]
  emit({'p':p,'orbital_digraphs_for_all_multiplicative_subgroups':count,'all_adjacencies_normal':True,'scope':'prime degree affine single nontrivial orbital; no claim covers all primitive groups'})
