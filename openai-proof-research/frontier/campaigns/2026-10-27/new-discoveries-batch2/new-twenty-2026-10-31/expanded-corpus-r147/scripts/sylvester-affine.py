import itertools,pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for dim in (4,5):
 start=time.monotonic();N=2**dim;fixed=[0]+[2**i for i in range(dim)];pool=[v for v in range(N) if v not in fixed];H=[[(-1)**((a&b).bit_count()%2) for b in range(N)] for a in range(N)];base=[sum(H[a][b] for a in fixed) for b in range(N)];best=10**8;count=0;bestC=None
 for rest in itertools.combinations(pool,11-len(fixed)):
  norm=sum(abs(base[b]+sum(H[a][b] for a in rest)) for b in range(N));count+=1
  # embedding in F2^5 repeats Walsh spectrum 2^(5-dim), complement size 11
  selected_norm=norm*2**(5-dim)+10
  if selected_norm<best:best,bestC=selected_norm,fixed+list(rest)
 out.append(dict(affine_dimension=dim,canonical_cases=count,best_selected_norm=best,complement=bestC,seconds=time.monotonic()-start))
print(out);(D/'outputs/sylvester5-affine.json').write_text(json.dumps(out,indent=2)+'\n')
