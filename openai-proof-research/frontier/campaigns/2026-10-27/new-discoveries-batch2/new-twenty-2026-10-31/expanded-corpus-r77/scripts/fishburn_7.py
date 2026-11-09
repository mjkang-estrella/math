import itertools as it,collections as C,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
def comp(n,k):
 if k==1:yield(n,);return
 for a in range(n+1):
  for b in comp(n-a,k-1):yield(a,)+b
for n in range(7,8):
 pc=C.Counter();pf=C.Counter();mc=C.Counter();mf=C.Counter();generated=0
 for p in it.permutations(range(n)):
  if any(p[j]==p[i]+1<p[i+1] for i in range(n-1) for j in range(i+2,n)):continue
  stat=(sum(all(p[j]<p[i] for j in range(i)) for i in range(n)),sum(all(p[j]>p[i] for j in range(i+1,n)) for i in range(n)),sum(all(p[j]<p[i] for j in range(i+1,n)) for i in range(n)),sum(all(p[j]>p[i] for j in range(i)) for i in range(n)))
  pc[stat]+=1
  if all(p[p[i]]==i for i in range(n)):pf[stat]+=1
 for d in range(1,n+1):
  cells=list(it.combinations_with_replacement(range(d),2))
  for a in comp(n,len(cells)):
   generated+=1;mat=dict(zip(cells,a))
   if any(not any(mat.get((i,j),0) for j in range(d)) or not any(mat.get((j,i),0) for j in range(d)) for i in range(d)):continue
   nz=[z for z,v in mat.items() if v];stat=(sum(v for (i,j),v in mat.items() if i==0),sum(v for (i,j),v in mat.items() if j==d-1),sum(not any(s<=i and t>=j and (s,t)!=(i,j) for s,t in nz) for i,j in nz),sum(i==j for i,j in nz));mc[stat]+=1
   if all(v==mat[d-1-j,d-1-i] for (i,j),v in mat.items()):mf[stat]+=1
 rows.append(dict(n=n,permutations=sum(pc.values()),matrices=sum(mc.values()),involutions=sum(pf.values()),symmetric_matrices=sum(mf.values()),generated_matrix_compositions=generated,distribution_equal=pc==mc,fixed_distribution_equal=pf==mf,fixed_differences={str(k):[pf[k],mf[k]] for k in pf.keys()|mf.keys() if pf[k]!=mf[k]}))
 (D/'outputs/search-fishburn-7.json').write_text(json.dumps(dict(id=340094,space='all permutations and all upper triangular nonnegative matrices weight n, dimensions1..n, n1..6; source pattern pi_i+1=pi_j<pi_(i+1); fixed-point refined obstruction for equivariant bijection',rows=rows),indent=2)+'\n');print(rows[-1],flush=True)
