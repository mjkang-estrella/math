import pathlib,itertools,json,math,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def coeff(m,s):
 return [x for x in itertools.product(range(-s,s+1),repeat=m) if sum(map(abs,x))<=s]
for m,s in [(3,2),(3,3),(4,2)]:
 C=coeff(m,s);N=len(C);cnt=0;found=[]
 groups=[(N,)]
 if (m,s)==(3,2):groups.append((5,5))
 if (m,s)==(3,3):groups.append((3,21))
 for shape in groups:
  elems=list(itertools.product(*(range(d) for d in shape)))
  # all unordered subsets of nonzero elements, no assumption about units.
  checked=0
  for A in itertools.combinations(elems[1:],m):
   checked+=1;seen=set();ok=True
   for c in C:
    y=tuple(sum(c[j]*A[j][a] for j in range(m))%shape[a] for a in range(len(shape)))
    if y in seen:ok=False;break
    seen.add(y)
   if ok:found.append(A)
  out.append({'m':m,'s':s,'shape':shape,'order':N,'subsets_checked':checked,'perfect':found})
  print(out[-1],flush=True)
(D/'outputs/spanning.json').write_text(json.dumps(out))
