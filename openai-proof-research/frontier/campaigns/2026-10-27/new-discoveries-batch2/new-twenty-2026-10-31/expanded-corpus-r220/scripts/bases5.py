import pathlib,json,itertools,random,math
L=pathlib.Path(__file__).resolve().parents[1];r=5;N=1<<r;full=(1<<N)-1
spaces={1:0};todo=[1]
while todo:
 W=todo.pop();d=spaces[W]
 if d==r:continue
 xs=[x for x in range(N) if W>>x&1]
 for x in range(1,N):
  if W>>x&1:continue
  U=W
  for y in xs:U|=1<<(x^y)
  if U not in spaces:spaces[U]=d+1;todo.append(U)
terms=[(W,(-1)**(r-d)*2**((r-d)*(r-d-1)//2)) for W,d in spaces.items()]
def score(S):return sum(mu*(S&W).bit_count()**r for W,mu in terms)//math.factorial(r)
rng=random.Random(220);out=[]
for c in (4,3,2):
 removed=1<<(r-c);target=full^((1<<removed)-1);baseline=score(target);best=baseline;bm=target;checked=0
 if c>=3:
  seq=(full^sum(1<<x for x in xs) for xs in itertools.combinations(range(N),removed))
 else:seq=(full^sum(1<<x for x in rng.sample(range(N),removed)) for _ in range(20000))
 for S in seq:
  checked+=1;v=score(S)
  if v>best:best=v;bm=S;print('new max',c,best,baseline,flush=True)
 out.append({'r':r,'c':c,'mode':'exhaustive' if c>=3 else 'uniform random seed 220','checked':checked,'proposed_bases':baseline,'best':best,'best_subset':bm})
 print(out[-1],flush=True);(L/'outputs/bases5-data.json').write_text(json.dumps(out,indent=2))
