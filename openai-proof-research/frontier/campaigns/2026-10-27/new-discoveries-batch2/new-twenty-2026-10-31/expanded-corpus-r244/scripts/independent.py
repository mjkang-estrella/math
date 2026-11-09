import itertools,math,sys,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
def check(n,edges):
 a=[0]*n
 for u,v in edges:a[u]|=1<<v;a[v]|=1<<u
 if min(s.bit_count() for s in a)<2:return None
 ind=[False]*(1<<n);ind[0]=True;cnt=[0]*(n+1);col=[0]+[n]*((1<<n)-1)
 for s in range(1,1<<n):
  b=s&-s;v=b.bit_length()-1;rest=s^b;ind[s]=ind[rest] and not(a[v]&rest)
  if ind[s]:cnt[s.bit_count()]+=1;col[s]=1
  else:
   sub=s
   while sub:
    if sub&b and ind[sub]:col[s]=min(col[s],1+col[s^sub])
    sub=(sub-1)&s
 k=col[-1]
 if k<4:return None
 conn=n-1
 for rem in range(1<<n):
  if rem.bit_count()>=conn:continue
  remain=((1<<n)-1)^rem;seen=remain&-remain;old=0
  while old!=seen:
   old=seen
   for v in range(n):
    if seen>>v&1:seen|=a[v]&remain
  if seen!=remain:conn=rem.bit_count()
 for l in range(2,min(k,conn+1)):
  for t in range(3,n+1):
   C=lambda m,r:math.comb(m,r) if m>=r>=0 else 0
   bound=C(n-k,t)+(k-l)*C(n-k,t-1)
   if cnt[t]>bound:return {'n':n,'edges':edges,'k':k,'l':l,'t':t,'count':cnt[t],'bound':bound}
 return (k,conn)
rows=[]
for n in range(4,int(sys.argv[1])+1):
 es=list(itertools.combinations(range(n),2));relevant=0
 for mask in range(1<<len(es)):
  result=check(n,[e for i,e in enumerate(es) if mask>>i&1])
  if isinstance(result,dict):print('COUNTEREXAMPLE',result,flush=True);raise SystemExit
  if result and result[1]>=2:relevant+=1
 row={'n':n,'labelled_graphs':1<<len(es),'chromatic_at_least_4_connectivity_at_least_2':relevant};rows.append(row);print(row,flush=True)
(D/f'independent-results-{sys.argv[1]}.json').write_text(json.dumps(rows,indent=2))
