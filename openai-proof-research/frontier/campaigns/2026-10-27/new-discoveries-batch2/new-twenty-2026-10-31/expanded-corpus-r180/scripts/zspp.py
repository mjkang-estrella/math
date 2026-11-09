import itertools as it,pathlib,json,functools,time
D=pathlib.Path(__file__).resolve().parents[1]
# Exact 3/4/5-block partitions suffice: every integer >=3 is a sum of 3,4,5.
# Gamma = C2^3 x C5; encode element by 5*x+y.
N=40; elems=list(range(1,N)); bysize={k:[] for k in (3,4,5)}
for k in bysize:
 for c in it.combinations(elems,k):
  x=0;y=0
  for a in c:x^=a//5;y+=a%5
  if not x and y%5==0:bysize[k].append(sum(1<<(a-1) for a in c))
print('zero-sum subset counts',{k:len(v) for k,v in bysize.items()},flush=True)
full=(1<<39)-1; outputs=[]
for a in range(14):
 for b in range(10):
  rest=39-3*a-4*b
  if rest<0 or rest%5:continue
  c=rest//5; calls=[0]
  @functools.lru_cache(maxsize=100000)
  def solve(mask,a,b,c):
   calls[0]+=1
   if not mask:return ()
   ks=[k for k,t in zip((3,4,5),(a,b,c)) if t]
   if a+b+c==1:
    return (mask,) if mask in sets[ks[0]] else None
   # pick smallest remaining point, then try blocks through it
   bit=mask&-mask
   for k in ks:
    for sub in index[k][bit.bit_length()-1]:
     if sub&mask!=sub:continue
     t=[a,b,c];t[k-3]-=1
     ans=solve(mask^sub,*t)
     if ans is not None:return (sub,)+ans
   return None
  sets={k:set(v) for k,v in bysize.items()}; index={k:[[s for s in v if s>>i&1] for i in range(39)] for k,v in bysize.items()}
  ans=solve(full,a,b,c)
  result={'counts_3_4_5':[a,b,c],'found':ans is not None,'calls':calls[0],'blocks':[[i+1 for i in range(39) if m>>i&1] for m in ans] if ans else None}
  outputs.append(result);print({k:v for k,v in result.items() if k!='blocks'},flush=True)
  (D/'outputs/zspp40.json').write_text(json.dumps(outputs,indent=2))
