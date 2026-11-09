import pathlib,itertools,math,json,time,sys
D=pathlib.Path(__file__).resolve().parents[1]; maxn=int(sys.argv[1]);maxm=int(sys.argv[2]);results=[]
def choose(a,b):
 if b==0:return 1
 return math.comb(a,b) if a>=b>=0 else 0
for n in range(2,maxn+1):
 roots=list(itertools.combinations(range(1,n+1),2));ix={r:i for i,r in enumerate(roots)}
 triples=[(ix[i,j],ix[j,k],ix[i,k]) for i,j,k in itertools.combinations(range(1,n+1),3)]
 filters=[b for b in range(1<<len(roots)) if all(not(b>>i&1) or all(b>>j&1 for j,s in enumerate(roots) if s[0]<=r[0] and s[1]>=r[1]) for i,r in enumerate(roots))]
 for m in range(1,maxm+1):
  for t in range(1,n+1):
   fs=[b for b in filters if all(not(b>>i&1) or r[1]>t for i,r in enumerate(roots))]
   count=0;pol={}
   def geometric(v):return all(min(m,v[a]+v[b])<=v[c]<=min(m,v[a]+v[b]+1) for a,b,c in triples)
   def visit(chain):
    global count
    if len(chain)<m:
     for b in fs:
      if not chain or b&chain[-1]==b:visit(chain+[b])
     return
    v=[sum(b>>i&1 for b in chain) for i in range(len(roots))]
    if not geometric(v):return
    count+=1;floors=[]
    for i,r in enumerate(roots):
     if v[i]!=m:continue
     v[i]-=1
     valid=geometric(v) and all(v[j]>=v[i] for j,s in enumerate(roots) if s[0]<=r[0] and s[1]>=r[1]) and all(v[j]<=v[i] for j,s in enumerate(roots) if s[0]>=r[0] and s[1]<=r[1])
     v[i]+=1
     if valid:floors.append(r)
    key=(len(floors),sum(j==i+1 and i>=t for i,j in floors));pol[key]=pol.get(key,0)+1
   visit([])
   pred={}
   for k in range(n-t+1):
    for h in range(n-t-k+1):
     val=choose(m*n-t+1,k)*choose(t+k+h-2,h)-m*choose(m*n-t,k-1)*choose(t+k+h-1,h)
     if val:pred[n-t-k,n-t-k-h]=val
   row={'n':n,'m':m,'t':t,'chains':count,'match':pol==pred,'observed':{str(k):v for k,v in sorted(pol.items())},'predicted':{str(k):v for k,v in sorted(pred.items())}};results.append(row);print(json.dumps(row),flush=True)
   if pol!=pred: print('FAIL',flush=True)
(D/f'outputs/htriangle-{maxn}-{maxm}.json').write_text(json.dumps(results,indent=2)+'\n')
