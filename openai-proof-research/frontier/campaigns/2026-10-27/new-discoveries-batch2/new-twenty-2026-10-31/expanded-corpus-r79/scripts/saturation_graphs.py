import pathlib,itertools as it,json
D=pathlib.Path(__file__).resolve().parents[1]
res=[]
for n in [3,4]:
 allE=list(it.combinations(range(n),2));m=len(allE)
 for name,v,pat in [('P3',3,[(0,1),(1,2)]),('K3',3,[(0,1),(0,2),(1,2)]),('2K2',4,[(0,1),(2,3)])]:
  emb=[tuple(tuple(sorted((p[a],p[b]))) for a,b in pat) for p in it.permutations(range(n),v)] if v<=n else []
  if not emb:continue
  def contains(order):
   r={e:j for j,e in enumerate(order)}
   return any(all(e in r for e in es) and all(r[es[j]]<r[es[j+1]] for j in range(len(es)-1)) for es in emb)
  cnt=0;answer=None
  for length in range(m+1):
   for order in it.permutations(allE,length):
    cnt+=1
    if contains(order):continue
    if all(contains(order[:j]+(e,)+order[j:]) for e in allE if e not in order for j in range(length+1)):answer=order;break
   if answer is not None:break
  res.append({'n':n,'target':name,'orders_examined':cnt,'minimum_witness':answer})
(D/'outputs/search-364185.json').write_text(json.dumps({'definition':'source Def2 sate: every missing edge and every insertion position in edge order must create an order-preserving noninduced target copy; host avoids target','scope':'ordered targets P3,K3,2K2 with displayed canonical edge orders; host orders n3,4 where n>=v(target), all ordered subsets until minimum witness; no asymptotic inference','cases':res},indent=2)+'\n')
res=[]
for n in [4,5,6]:
 E=list(it.combinations(range(n),2));idx={e:j for j,e in enumerate(E)};copies=[[idx[e] for e in it.combinations(S,2)] for S in it.combinations(range(n),4)];nodes=[0]
 for colors in range(1,5):
  a=[]
  def rec():
   nodes[0]+=1
   if nodes[0]>500000:return None
   j=len(a)
   if any(max(c)<j and all(sum(a[x]==z for x in c)%2==0 for z in range(colors)) for c in copies):return None
   if j==len(E):return a.copy()
   for z in range(min(colors,max(a,default=-1)+2)):
    a.append(z);r=rec()
    if r is not None:return r
    a.pop()
   return None
  r=rec()
  if r is not None or nodes[0]>500000:break
 res.append({'n':n,'colors':colors,'nodes':nodes[0],'witness':r,'capped':nodes[0]>500000})
(D/'outputs/search-360560.json').write_text(json.dumps({'definition':'r_H(n) minimum colors avoiding a copy H for which every color appears evenly; H=K4 has no even decomposition (source)','scope':'H=K4, n4,5,6; exact restricted-growth colorings until witness at minimal tested colors; 500000nodes total cap per n. These do not test subpolynomial growth.','cases':res},indent=2)+'\n')
