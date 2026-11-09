import pathlib,itertools,functools,json,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for mods in [(4,3,3),(2,5,5),(2,3,9),(2,3,3,3),(8,3,3),(2,3,3,5),(4,5,5)]:
 G=list(itertools.product(*[range(m) for m in mods]));R=[x for x in G if any(x) and any(2*a%m for a,m in zip(x,mods))];index={x:i for i,x in enumerate(R)};N=len(R)
 neg=lambda x:tuple(-a%m for a,m in zip(x,mods))
 triples=set()
 for i in range(N):
  for j in range(i+1,N):
   z=tuple((-a-b)%m for a,b,m in zip(R[i],R[j],mods));k=index.get(z,-1)
   if k<=j:continue
   inds={i,j,k,index[neg(R[i])],index[neg(R[j])],index[neg(R[k])]}
   if len(inds)==6:triples.add(sum(1<<v for v in inds))
 triples=sorted(triples)
 # A packing of floor(N/6) inversion-symmetric zero-sum triple-pairs
 # certifies all 2/3 refinements, and hence all partitions with parts >=2.
 @functools.lru_cache(None)
 def solve(mask,need,start):
  if need==0:return ()
  if mask.bit_count()<6*need:return None
  for j in range(start,len(triples)):
   t=triples[j]
   if t&mask==t:
    s=solve(mask^t,need-1,j+1)
    if s is not None:return (t,)+s
  return None
 cert=solve((1<<N)-1,N//6,0)
 if cert is not None:
  used=0
  for t in cert:
   assert t.bit_count()==6 and used&t==0;used|=t
  for c in range(0,2*(N//6)+1,2):assert (N-3*c)%2==0
 row={'moduli':mods,'order':len(G),'R_size':N,'triple_pairs_available':len(triples),'packed_triple_pairs':len(cert) if cert is not None else None,'mask_certificate':cert,'consequence':'all integer partitions with parts >=2 by 2/3 refinement and retaining unused inverse pairs' if cert is not None else 'none','credit':'finite diagnostic only; Skolem-type source mechanism; no new family claim'};out.append(row);print(row,flush=True);(D/'outputs/groups-extended.json').write_text(json.dumps(out,indent=2)+'\n')
