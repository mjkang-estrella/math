import itertools,math,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for k in (2,3,4):
 n=4*k;sub=list(itertools.combinations(range(n),k));count=0;best=math.comb(n,k);bestw=None
 for w in itertools.combinations_with_replacement(range(-2,3),n):
  if sum(w)<0:continue
  nonneg=sum(sum(w[i] for i in s)>=0 for s in sub);count+=1
  assert nonneg>=math.comb(n-1,k-1)
  if nonneg<best:best,bestw=nonneg,w
 out.append(dict(n=n,k=k,sorted_integer_weight_vectors=count,range=[-2,2],min_nonnegative=best,bound=math.comb(n-1,k-1),witness=bestw))
print(out);(D/'outputs/mms.json').write_text(json.dumps(out,indent=2)+'\n')
