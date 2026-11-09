import itertools,collections,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);pos=collections.Counter();neg=collections.Counter()
for pi in itertools.permutations(range(1,n+1)):
 hat=[0]*n
 for a,b in zip(pi,pi[1:]):hat[a-1]=b
 h=[v for v in hat if v];des=sum(a>b for a,b in zip(h,h[1:]));asc=n-2-des
 ep=pi[-2:]==(2,1) or pi[-2:]==(n-1,n)
 corner=pi[-3:]==(n-1,1,n) or pi[-3:]==(2,n,1)
 collapsed=False
 if pi[-1] not in (1,n):
  x=pi.index(pi[-1]+1);y=pi.index(pi[-1]-1)
  # invalidity of the minimal segmentation, directly Definition 3.5
  bars=[i+1 for i in range(n-1) if hat[i] and next((v for v in hat[i+1:] if v),0)>hat[i]]
  z=tuple(sum(b<v for b in bars) for v in pi[:-1]);p=z[x:];q=z[y:];collapsed=p==q+q or q==p+p
 pos[1+des+ep]+=1;neg[1+asc+(corner or collapsed)]+=1
result={'n':n,'permutations':sum(pos.values()),'positive':dict(sorted(pos.items())),'negative':dict(sorted(neg.items())),'inequality':all(sum(pos[j] for j in pos if j<=k)<=sum(neg[j] for j in neg if j<=k) for k in range(2,n+1))}
print(result);(D/f'outputs/signed{n}.json').write_text(json.dumps(result,indent=2)+'\n')
