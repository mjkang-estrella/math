import math,itertools,random,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];random.seed(105)
vec=set()
for m in range(2,35):
 for n in range(1,m):
  if math.gcd(m,n)==1 and (m-n)%2:
   a,b=m*m-n*n,2*m*n
   for x,y in [(a,b),(b,a),(a,-b),(b,-a)]:vec.add((x,y))
vec=sorted(vec,key=lambda v:sum(abs(x) for x in v))[:150]
pairs=[(a,b,a[0]*b[1]-a[1]*b[0]) for a,b in itertools.combinations(vec,2) if a[0]*b[1]!=a[1]*b[0]]
points=list(itertools.product(range(101),repeat=2))+[(random.randrange(4000,100001),random.randrange(0,100001)) for _ in range(5000)]
known={(1,0),(0,1),(2,0),(0,2),(2,1),(1,2)};miss=[];found=0;ones=0;cert=[]
for g,h in points:
 if (g,h)==(0,0) or (g*h!=0 and math.isqrt(g*g+h*h)**2==g*g+h*h):ones+=1;continue
 if (g,h) in known:continue
 ok=False
 for a,b,d in pairs:
  k=g*b[1]-h*b[0];l=a[0]*h-a[1]*g
  if k%d==0 and l%d==0:
   k//=d;l//=d
   if k and l:
    found+=1;ok=True
    if len(cert)<100:cert.append(dict(point=[g,h],a=a,b=b,k=k,l=l))
    break
 if not ok:miss.append([g,h])
z=dict(points=len(points),distance_zero_or_one=ones,two_step_witnesses=found,known_exceptions_skipped=6,primitive_directions=vec,unresolved=miss,sample_witnesses=cert,limitation='Failure of this finite direction dictionary is not proof of distance three. Positive witnesses use nonzero integer multiples of primitive Pythagorean vectors.')
(D/'outputs/pythagorean.json').write_text(json.dumps(z,indent=2));print('points',len(points),'two_step',found,'unresolved',len(miss),miss[:20])
