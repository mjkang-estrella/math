import pathlib,json,fractions,math
D=pathlib.Path(__file__).resolve().parents[1];z=json.loads((D/'outputs/submod-dual-min.json').read_text());supp=z['support'];orbit=z['orbit'];F=fractions.Fraction
rows=[{} for x in z['reps']]+[{}];rhs=[F(0)]*len(z['reps'])+[F(1)]
for j,a in enumerate(supp):
 if a['kind']=='submodular':
  for x,c in a['terms']:
   k=orbit[x];rows[k][j]=rows[k].get(j,F(0))+c
 else:
  k=orbit[a['point']];rows[k][j]=F(1 if a['kind']=='good' else -1)
  if a['kind']=='good':rows[-1][j]=F(1)
basis={}
for a,b in zip(rows,rhs):
 a={j:v for j,v in a.items() if v}
 while a:
  p=min(a);v=a[p]
  if p not in basis:
   basis[p]=({j:t/v for j,t in a.items()},b/v);break
  c,d=basis[p]
  for j,t in c.items():
   a[j]=a.get(j,F(0))-v*t
   if not a[j]:del a[j]
  b-=v*d
 else:assert b==0,'inconsistent support'
print('rank',len(basis),'support',len(supp),flush=True)
x=[F(0)]*len(supp)
for p,(a,b) in sorted(basis.items(),reverse=True):x[p]=b-sum(t*x[j] for j,t in a.items() if j!=p)
assert all(v>=0 for v in x), 'negative exact weights'
assert all(sum(v*x[j] for j,v in a.items())==b for a,b in zip(rows,rhs))
den=math.lcm(*(v.denominator for v in x));out=[]
for a,v in zip(supp,x):
 if v:out.append(dict(a,weight=int(v*den)))
z.update(support=out,exact_balance=True,denominator=den,exact_method='Sparse Fraction Gaussian elimination of dual basic support. All weights nonnegative; all coefficient equations verified exactly.')
(D/'outputs/submod-dual-exact.json').write_text(json.dumps(z,indent=2));print('exact',len(out),'den',den,'maxweight',max(a['weight'] for a in out),flush=True)
