import itertools,json,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1]; out=[]
for r in range(2,5):
 for a in itertools.combinations_with_replacement(range(3,8),r):
  m=1+sum(x-1 for x in a)
  if m>9 or max(a)<4:continue
  e=[(0,1)];n=2
  for x in a:
   last=0
   for j in range(x-2):e.append((last,n));last=n;n+=1
   e.append((last,1))
  best=n;witness=None;count=0;valid=0
  for p in itertools.permutations(range(1,m+1)):
   count+=1;s=[0]*n
   for (u,v),x in zip(e,p):s[u]+=x;s[v]+=x
   if any(s[u]==s[v] for u,v in e):continue
   valid+=1;c=len(set(s))
   if c<best:best=c;witness=p
  row=dict(a=a,edges=e,n=n,m=m,permutations=count,valid=valid,minimum=best,witness=witness)
  out.append(row);print(json.dumps(row),flush=True)
(D/'labels-coverage.json').write_text(json.dumps(out,indent=2))
