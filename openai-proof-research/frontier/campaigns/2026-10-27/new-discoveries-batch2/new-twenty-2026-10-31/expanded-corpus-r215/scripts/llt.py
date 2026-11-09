import pathlib,sys,itertools,math,json,time,collections
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import sympy as sp
start=time.monotonic();out=[]
def parts(n,m=None):
 if n==0:yield ();return
 for a in range(min(n,m or n),1-1,-1):
  for p in parts(n-a,a):yield (a,)+p
for n in range(2,5):
 ps=list(parts(n));reps=[p+(0,)*(n-len(p)) for p in ps];basis=[]
 for p in ps:
  poly={(0,)*n:1}
  for size in p:
   nxt=collections.Counter()
   for exp,v in poly.items():
    for sub in itertools.combinations(range(n),size):
     e=list(exp)
     for a in sub:e[a]+=1
     nxt[tuple(e)]+=v
   poly=nxt
  basis.append([poly.get(rep,0) for rep in reps])
 inv=sp.Matrix(basis).T.inv();counts=0
 for area in itertools.product(range(n),repeat=n):
  if any(area[i]-1>area[(i+1)%n] for i in range(n)):continue
  edges={(i,(i+r)%n) for i,a in enumerate(area) for r in range(1,a+1)}
  # Restrict to source corners with both predecessor edges genuinely present;
  # diagonal-boundary corners are deliberately omitted rather than guessed.
  corners=[(i,j) for i in range(n) for j in range(n) if i!=j and (i,j) not in edges and (i,(j-1)%n) in edges and ((i+1)%n,j) in edges]
  for mask in range(1,1<<len(corners)):
   strict=[e for i,e in enumerate(corners) if mask>>i&1];k=len(strict);coef={rep:[0]*(len(edges)+k+1) for rep in reps}
   for colors in itertools.product(range(n),repeat=n):
    exp=tuple(colors.count(i) for i in range(n))
    if exp not in coef:continue
    asc=sum(colors[i]<colors[j] for i,j in edges)
    fullasc=asc+sum(colors[i]<colors[j] for i,j in strict)
    for r in range(fullasc+1):coef[exp][r]+=math.comb(fullasc,r)
    if all(colors[i]<colors[j] for i,j in strict):
     for r in range(asc+1):coef[exp][r+k]-=math.comb(asc,r)
   ecoeff=[]
   for r in range(len(edges)+k+1):ecoeff.append(list(inv*sp.Matrix([coef[e][r] for e in reps])))
   assert all(x>=0 for row in ecoeff for x in row),(area,strict,ecoeff)
   counts+=1
 out.append({'n':n,'cases':counts,'status':'nonnegative e coefficients in inspected restricted-corner family'})
 print(out[-1],flush=True)
(D/'outputs/llt-corrected.json').write_text(json.dumps({'results':out,'scope':'n<=4 circular area sequences; nonempty subsets of corners with both predecessor edges actually present. Gamma includes selected corners as ordinary ascents; H marks those edges strict and removes them from ascent statistic. Symmetry supplied by source, not independently certified. Exact rational basis conversion; diagnostic only.'},indent=2)+'\n')
