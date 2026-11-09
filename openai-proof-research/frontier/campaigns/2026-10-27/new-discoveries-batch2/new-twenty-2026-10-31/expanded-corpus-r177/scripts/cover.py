import pathlib,json,itertools,time,sys
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);ellmax=int(sys.argv[2]);stop=time.monotonic()+105
# tuples indexed x_n,y_n,...,x_1,y_1, in descending lexical variable order
ix=lambda i:2*(n-1-i)
iy=lambda i:ix(i)+1
opts=[(ix(i),ix(j)) for i in range(n) for j in range(i+1,n)]+[(ix(i),iy(j)) for i in range(n) for j in range(i+1,n)]
base=[(ix(i),iy(i)) for i in range(n)];valid=0;tested=0;bad=[];incomplete=False

def cols(gs):
 out=[]
 for k,g in enumerate(gs):
  ds=[tuple(max(0,a-b) for a,b in zip(h,g)) for h in gs[:k]]
  singles={next(i for i,a in enumerate(d) if a) for d in ds if sum(d)==1}
  if any(not any(d[i] for i in singles) for d in ds):return None,k
  out.append(singles)
 return out,None
for mask in range(1<<len(opts)):
 if time.monotonic()>stop:incomplete=True;break
 edges=base+[e for j,e in enumerate(opts) if mask>>j&1];E={frozenset(e) for e in edges}
 if any(frozenset((ix(i),iy(j))) in E and frozenset((ix(i),ix(j))) in E for i in range(n) for j in range(i+1,n)):continue
 if any(frozenset((z,ix(j))) in E and frozenset((iy(j),ix(k))) in E and frozenset((z,ix(k))) not in E for i,j,k in itertools.permutations(range(n),3) for z in [ix(i),iy(i)]):continue
 covers=[];unmixed=True
 for c in range(1<<(2*n)):
  if not all(c>>a&1 or c>>b&1 for a,b in edges):continue
  if any(all((c^(1<<v))>>a&1 or (c^(1<<v))>>b&1 for a,b in edges) for v in range(2*n) if c>>v&1):continue
  if c.bit_count()!=n:unmixed=False;break
  covers.append(tuple(c>>v&1 for v in range(2*n)))
 if not unmixed:continue
 valid+=1;gs={(0,)*(2*n)}
 for ell in range(1,ellmax+1):
  gs={tuple(a+b for a,b in zip(g,h)) for g in gs for h in covers};ordered=sorted(gs,reverse=True);C,k=cols(ordered);tested+=1
  if C is None:bad.append({'mask':mask,'ell':ell,'homological_index':0,'failed_generator':k});continue
  for hidx in range(1,2*n+1):
   hs=set()
   for g,co in zip(ordered,C):
    for s in itertools.combinations(co,hidx):hs.add(tuple(a+(v in s) for v,a in enumerate(g)))
   if not hs:break
   cc,k=cols(sorted(hs,reverse=True));tested+=1
   if cc is None:bad.append({'mask':mask,'ell':ell,'homological_index':hidx,'failed_generator':k})
 if bad:break
r={'n_pairs':n,'ell_max':ellmax,'masks_total':1<<len(opts),'masks_completed_before':mask,'CM_graphs':valid,'shift_ideals_checked':tested,'bad':bad,'time_stop':incomplete};(D/f'outputs/cover{n}-{ellmax}.json').write_text(json.dumps(r,indent=2));print(r)
