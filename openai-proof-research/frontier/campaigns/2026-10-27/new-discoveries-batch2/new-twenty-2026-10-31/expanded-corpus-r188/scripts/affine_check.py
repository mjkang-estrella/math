from fractions import Fraction as F
import itertools,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);k=int(sys.argv[2]);out={}
for sig in itertools.product([1,-1],repeat=k):
 patterns=set()
 for word in itertools.product(range(k),repeat=n-1):
  # Inverse branches send the free final coordinate y in (0,1) to initial x.
  aff=[(1,0)]
  a,b=1,0
  for letter in reversed(word):
   a,b=(a/k,(b+letter)/k) if sig[letter]==1 else (-a/k,(letter+1-b)/k)
  # use exact integer slopes for F^j(x), and exact cylinder interval
  low=F(0);high=F(1)
  for letter in reversed(word):
   low,high=((low+letter)/k,(high+letter)/k) if sig[letter]==1 else ((letter+1-high)/k,(letter+1-low)/k)
  a,b=1,0;aff=[(a,b)]
  for letter in word:
   a,b=(k*a,k*b-letter) if sig[letter]==1 else (-k*a,letter+1-k*b)
   aff.append((a,b))
  cuts={low,high}
  for (a,b),(c,d) in itertools.combinations(aff,2):
   if a!=c:
    z=F(d-b,a-c)
    if low<z<high:cuts.add(z)
  cuts=sorted(cuts)
  for l,h in zip(cuts,cuts[1:]):
   x=(l+h)/2;vals=[a*x+b for a,b in aff]
   if len(set(vals))<n:continue
   patterns.add(tuple(sorted(range(n),key=lambda j:vals[j])))
 s=''.join('+' if z==1 else '-' for z in sig);out[s]=len(patterns)
print(out);prior=json.loads((D/f'outputs/signed-n{n}-k{k}.json').read_text())['counts'];print('matches',prior==out)
(D/f'outputs/affine-n{n}-k{k}.json').write_text(json.dumps({'counts':out,'matches_segmentation':prior==out},indent=2))
