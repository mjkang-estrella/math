import pathlib,json,random,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(369935);out=[]
def test(fs):
 n=len(fs[0])-1;p=len(set().union(*map(set,fs)));t=len(fs)
 if t!=p-n:return
 counts=[len(set().union(*(set(itertools.combinations(sorted(f),k+1)) for f in fs))) for k in range(n)]
 import math
 ks=[k for k in range(1,n) if counts[k]==t*math.comb(n,k)+math.comb(n,k+1)]
 if not ks:return
 # current v3 circuits; incidence forest required
 par=list(range(t)); ridges={}
 def find(a):
  while par[a]!=a:a=par[a]
  return a
 for i,f in enumerate(fs):
  for r in itertools.combinations(sorted(f),n):
   if r in ridges:
    j=ridges[r];x,y=find(i),find(j)
    if x==y:return
    par[x]=y
   else:ridges[r]=i
 if len({find(i) for i in range(t)})==1:return
 return {'n':n,'p':p,'facets':fs,'counts':counts,'matched_k':ks}
trials=0
for n in [3,4,5]:
 for size in [6,8,10,14,18,24]:
  hits=0
  for rep in range(15000):
   trials+=1
   fs=[tuple(range(n+1))];nxt=n+1
   for i in range(1,size):
    f=fs[-1] if rep%2 else rng.choice(fs)
    r=rng.sample(f,n)
    if rng.random()<.36 and nxt>n+1:
     v=rng.choice([v for v in range(nxt) if v not in r])
    else:v=nxt;nxt+=1
    f=tuple(sorted(r+[v]));
    if f in fs:break
    fs.append(f)
   else:
    # add 1-3 disjoint facets then require correct global vertex count
    for c in range(1,4):
     extra=[tuple(range(nxt+j*(n+1),nxt+(j+1)*(n+1))) for j in range(c)]
     a=test(fs+extra)
     if a:
      hits+=1;out.append(a);print('WITNESS',json.dumps(a),flush=True)
      (D/'outputs/simplicial-structured-witness.json').write_text(json.dumps(a,indent=2)+'\n');sys.exit()
  print('block',n,size,'trials',rep+1,'hits',hits,flush=True)
(D/'outputs/simplicial-structured.json').write_text(json.dumps({'trials':trials,'witnesses':out})+'\n')
