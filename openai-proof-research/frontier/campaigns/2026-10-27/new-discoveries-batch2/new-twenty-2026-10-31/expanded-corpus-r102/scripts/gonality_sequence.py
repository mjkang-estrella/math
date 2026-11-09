import pathlib,json,itertools,functools,time
D=pathlib.Path(__file__).resolve().parents[1]
exec((D/'scripts/gonality.py').read_text().split('for n,mm in')[0])
start=time.monotonic();done=0;fail=[]
for line in (D/'outputs/gonality-deep.jsonl').read_text().splitlines():
 o=json.loads(line);n=o['n']
 for graph in o['tight']:
  k,g=graph['k'],graph['g']
  if k<3:continue
  L=[[0]*n for _ in range(n)]
  for (a,b),m in graph['edges']:L[a][a]+=m;L[b][b]+=m;L[a][b]-=m;L[b][a]-=m
  A=[r[:-1] for r in L[:-1]];den=det(A);adj=[[(-1)**(i+j)*det([r[:i]+r[i+1:] for h,r in enumerate(A) if h!=j]) for j in range(n-1)]for i in range(n-1)]
  def cls(v):return tuple(sum(a*b for a,b in zip(row,v))%den for row in adj)
  def sub(a,b):return tuple((x-y)%den for x,y in zip(a,b))
  C=[{cls(v) for v in comps(d,n)} for d in range(2*g+1)]
  def good(d,r):return {a for a in C[d] if all(sub(a,e) in C[d-r] for e in C[r])}
  D2=good(k+1,2);checks=[]
  for r in range(1,g+1):
   if r==g:expected=2*g
   else:
    l,h=next((l,h) for l in range(1,k-1) for h in range(l+1) if r==l*(l+3)//2-h);expected=l*(k+1)-h
   upper=good(expected,r);lower=good(expected-1,r)
   ok=bool(upper) and not lower;checks.append({'r':r,'expected':expected,'upper_classes':len(upper),'lower_classes':len(lower)})
   if not ok:fail.append({'graph':graph,'r':r,'checks':checks[-1]})
  uniqueness=[]
  for l in range(1,k-1):
   r=l*(l+3)//2;actual=good(l*(k+1),r);predicted={tuple(l*x%den for x in c) for c in D2}
   uniqueness.append({'l':l,'classes':len(actual),'predicted_classes':len(predicted),'equal':actual==predicted})
   if len(actual)!=1 or actual!=predicted:fail.append({'graph':graph,'uniqueness':uniqueness[-1]})
  done+=1
  print(json.dumps({'n':n,'k':k,'g':g,'edges':graph['edges'],'gonality_checks':checks,'uniqueness':uniqueness,'cumulative':done,'failures':fail,'seconds':time.monotonic()-start}),flush=True)
