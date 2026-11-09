import numpy as np,json,pathlib,itertools,math,random,time
D=pathlib.Path(__file__).resolve().parents[1];out={}
# 372013: weighted tournament kernels; exact doubled matrices on exhaustive order <=4.
best=(0,None); count=0
for n in range(2,5):
 es=list(itertools.combinations(range(n),2))
 for bits in range(1<<len(es)):
  B=np.eye(n,dtype=object)
  for e,(i,j) in enumerate(es): B[i,j],B[j,i]=(2,0) if bits>>e&1 else (0,2)
  vv=[np.ones(n,dtype=object)]
  for k in range(1,25):vv.append(B@vv[-1])
  for k in range(3,25):
   for a in range(1,k):
    # 1^T B^a (B^T)^b 1 = inner((B^T)^a 1,(B^T)^b 1)
    # equivalently reverse tournament, all tournaments enumerated.
    num=sum(vv[a][i]*vv[k-a][i] for i in range(n));den=n**(k+1);count+=1
    if num>den:raise RuntimeError(('witness',n,bits,k,a,num,den))
out['372013']={'space':'all tournaments of orders 2,3,4, diagonal 1/2; every one-flip path length 3..24, each split','tests':count,'counterexample':None}
# 362719 parity truth table for every source map, all 4 letters.
maps=[(0,2,3,1),(1,0,2,3),(1,3,2,0),(3,1,0,2),(3,2,0,1),(2,0,1,3),(2,3,1,0),(0,1,3,2)]
out['362719']={'map_parity_offsets':[[x.bit_count()%2^(i%2) for i,x in enumerate(m)] for m in maps],'argument':'Each row constant, so equal quaternary sum mod4 forces equal image-weight parity. Single-deletion overlap forces weight difference at most1, hence equal. Routine generic parity consequence.'}
# Comma graph finite trajectories memoized, boundary escape is not infinity.
res=[]
for b in range(3,17):
 limit=250000; succ=[0]*(limit+1)
 def lead(v):
  while v>=b:v//=b
  return v
 for v in range(1,limit+1):
  succ[v]=next((v+(v%b)*b+d for d in range(1,b) if lead(v+(v%b)*b+d)==d),0)
 lengths=[0]*(limit+1); dead=0;escape=0;mx=0
 for v in range(limit,0,-1):
  s=succ[v]
  if s==0:lengths[v]=1;dead+=1
  elif s>limit:lengths[v]=-1;escape+=1
  elif lengths[s]<0:lengths[v]=-1;escape+=1
  else:lengths[v]=1+lengths[s];dead+=1;mx=max(mx,lengths[v])
 res.append({'base':b,'all_starts':limit,'proven_terminate_in_box':dead,'escape_box':escape,'max_finite_vertices':mx})
out['361614']=res
(D/'outputs/early.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
