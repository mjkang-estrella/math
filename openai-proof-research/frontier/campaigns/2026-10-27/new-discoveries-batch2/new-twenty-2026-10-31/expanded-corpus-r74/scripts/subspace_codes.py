import os,resource,pathlib,json,itertools
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);D=pathlib.Path(__file__).resolve().parents[1]
def mul(a,b):
 c=0
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
  if a&16:a^=19
 return c
code=[sum(1<<(x+16*(mul(a,x)^mul(b,mul(x,x)))) for x in range(1,16)) for a in range(16) for b in range(16)];code.append(sum(1<<(16*x) for x in range(1,16)));assert len(set(code))==257
pairs=0
for a,b in itertools.combinations(code,2):assert (a&b).bit_count()<=1;pairs+=1
count=0;compatible=[];already=set(code)
for piv in itertools.combinations(range(8),4):
 free=[(r,c) for r in range(4) for c in range(piv[r]+1,8) if c not in piv]
 for mask in range(1<<len(free)):
  rows=[1<<p for p in piv]
  for j,(r,c) in enumerate(free):
   if mask>>j&1:rows[r]|=1<<c
  span=[0]
  for r in rows:span+= [x^r for x in span]
  S=sum(1<<x for x in span if x);count+=1
  if S in already:continue
  if all((S&T).bit_count()<=1 for T in code):compatible.append(rows)
out={'id':381397,'q':2,'k':4,'space':'all 4-subspaces in F2^8, represented uniquely by RREF; test one-subspace extension of the standard lifted Gabidulin code plus vertical space','subspaces_enumerated':count,'seed_code_size':len(code),'seed_pairs_verified':pairs,'extensions':compatible,'limitation':'exhaustive one-extension diagnostic of a known code, not all codes; does not resolve other q,k'};(D/'outputs/subspace-search.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
