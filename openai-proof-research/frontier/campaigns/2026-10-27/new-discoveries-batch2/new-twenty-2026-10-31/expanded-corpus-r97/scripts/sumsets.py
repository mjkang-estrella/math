import itertools,math,json,pathlib,random
D=pathlib.Path(__file__).resolve().parents[1];out=[];rng=random.Random(97001)
for h,k in [(4,8),(5,7),(5,8),(6,7)]:
 lo=h*k-h+1;hi=math.comb(h+k-1,h); exc={lo+l*h+j for l in range(min(h,k)-2) for j in range(1,h-1-l)};found={};count=0
 def test(A):
  global count
  bits=1
  for _ in range(h):
   nxt=0
   for a in A:nxt |= bits<<a
   bits=nxt
  z=bits.bit_count();count+=1
  if z in exc:raise RuntimeError((h,k,A,z))
  if z not in found:found[z]=A
 for rest in itertools.combinations(range(1,19),k-1):test((0,)+rest)
 for _ in range(20000):
  cap=rng.choice([32,64,128,512,2048]);test(tuple(sorted({0,*rng.sample(range(1,cap),k-1)})))
 # generalized separated progressions to reach largest cardinalities
 for j in range(k):
  for cap in range(k,300):test(tuple(range(j))+tuple(cap*(h+1)**i for i in range(k-j)))
 row={'h':h,'k':k,'tests':count,'exhaustive_box':'0 in A subset [0,18], |A|=k','random_seed':97001,'exceptions':sorted(exc),'attained':{str(z):A for z,A in sorted(found.items())},'unattained_in_search':sorted(set(range(lo,hi+1))-exc-found.keys()),'warning':'finite unattained values do not prove impossible sizes; only witnesses are certified by Python integer arithmetic'}
 out.append(row);print({q:v for q,v in row.items() if q!='attained'},flush=True)
(D/'outputs/sumsets.json').write_text(json.dumps(out,indent=2)+'\n')
