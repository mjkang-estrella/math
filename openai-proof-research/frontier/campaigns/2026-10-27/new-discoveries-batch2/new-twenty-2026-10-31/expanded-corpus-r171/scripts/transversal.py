import pathlib,itertools,json,random,sys
D=pathlib.Path(__file__).resolve().parents[1]
rng=random.Random(171)
def score(T,q,r):
 return len({tuple((a[i]-b[i])%q for i in range(r)) for a in T for b in T})
out=[]
# Translation-normalized exhaustive rank-one sections; source has already proved this case.
for p in [3,5]:
 vals=[]
 for f in itertools.product(range(p),repeat=p-1):
  T=[0]+[i+p*f[i-1] for i in range(1,p)]
  vals.append(len({(a-b)%(p*p) for a in T for b in T}))
 out.append(dict(p=p,r=1,sections=len(vals),minimum=min(vals),expected=2*p-1))
# Structured rank-three p=3: all 3^9 scalar liftings f:(F3)^2->F3 in last coordinate.
# T={(a,b,c+3*f(a,b))}. This is not exhaustive among arbitrary vector liftings.
p=3; r=3; best=999;hist={}
for f in itertools.product(range(p),repeat=8):
 f=(0,)+f
 # Difference support factors into 5 possibilities in c and sets of shifted multiples in c.
 T=[(a,b,c+3*f[3*a+b]) for a in range(3) for b in range(3) for c in range(3)]
 s=score(T,9,3);hist[s]=hist.get(s,0)+1;best=min(best,s)
out.append(dict(p=3,r=3,sections=3**8,description='normalized scalar lifting of last coordinate depending on first two residues',minimum=best,expected=125,histogram=hist))
(D/'outputs/transversal.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
