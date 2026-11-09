import itertools,random,json,pathlib,sys
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(148)
def betti(sides,m):
 c=len(sides);full=(1<<m)-1;cells=[[] for _ in range(c+1)]
 for face in itertools.product([-1,0,1],repeat=c):
  cover=0
  for j,s in enumerate(face):
   if s>=0:cover|=sides[j][s]
  if cover==full:cells[face.count(-1)].append(face)
 rank=[0]*(c+2)
 rank[0]=int(bool(cells[0]))
 for d in range(1,c+1):
  idx={f:i for i,f in enumerate(cells[d-1])};basis={}
  for f in cells[d]:
   bits=0
   for i in range(c):
    if f[i]==-1:
     for b in [0,1]:bits^=1<<idx[f[:i]+(b,)+f[i+1:]]
   while bits:
    p=bits.bit_length()-1
    if p in basis:bits^=basis[p]
    else:basis[p]=bits;break
  rank[d]=len(basis)
 return ([int(not cells[0])]+[len(cells[d])-rank[d]-rank[d+1] for d in range(c+1)]),list(map(len,cells))
out=[]
for m,c,reps in [(2,2,500),(2,3,500),(3,3,1000),(3,4,3000),(3,5,2000),(4,5,3000),(4,6,1500)]:
 k=c-m;nonzero=0;hyp=0
 for t in range(reps):
  masks=list(range(1,1<<m));weights=[3 if x.bit_count()==1 else 1 for x in masks];sides=[tuple(rng.choices(masks,weights,k=2)) for _ in range(c)]
  b,sz=betti(sides,m)
  if b[k+1]==0:continue
  nonzero+=1
  if any(any(betti([(a&~(1<<i),b&~(1<<i)) for a,b in sides],m)[0][:k+2]) for i in []):pass
  # Delete a color by compressing its bit position, then test all reduced degrees -1 through k.
  deletions=[]
  for i in range(m):
   compress=lambda x:(x&((1<<i)-1))|((x>>(i+1))<<i)
   deletions.append(betti([(compress(a),compress(b)) for a,b in sides],m-1)[0])
  if any(any(x[:k+2]) for x in deletions):continue
  hyp+=1
  conclusion=all(any(a==1<<i or b==1<<i for a,b in sides) for i in range(m))
  if not conclusion:
   print('CANDIDATE',m,c,sides,b,deletions,flush=True);(L/'outputs/colorful-candidate.json').write_text(json.dumps({'m':m,'c':c,'sides':sides,'betti':b,'deletions':deletions}));raise SystemExit
 out.append({'m':m,'c':c,'k':k,'trials':reps,'nonzero_Hk':nonzero,'all_hypotheses':hyp});print(out[-1],flush=True);(L/'outputs/colorful.json').write_text(json.dumps(out,indent=2))
