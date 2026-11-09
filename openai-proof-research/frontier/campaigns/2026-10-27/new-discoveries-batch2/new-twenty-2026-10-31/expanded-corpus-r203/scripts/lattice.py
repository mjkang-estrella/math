import itertools,json,sys
norm=lambda x,y:x*x+x*y+y*y
vals=sorted({norm(x,y) for x in range(-10,11) for y in range(-10,11)}-{0})[:int(sys.argv[1])]
points=[(x,y) for x in range(-10,11) for y in range(-10,11) if norm(x,y)<=vals[-1]]
rows=[];best={7:0,8:0}
def clique(adj):
 out=[]
 def go(R,P):
  nonlocal out
  if len(R)+P.bit_count()<=len(out):return
  order=[];bounds=[];Q=P;c=0
  while Q:
   c+=1;avail=Q
   while avail:
    b=avail&-avail;v=b.bit_length()-1;Q^=b;avail^=b;avail&=~adj[v];order.append(v);bounds.append(c)
  for v,bound in zip(order[::-1],bounds[::-1]):
   if len(R)+bound<=len(out):return
   go(R+[v],P&adj[v]);P&=~(1<<v)
  if len(R)>len(out):out=R
 go([],(1<<len(adj))-1);return out
for m in [7,8]:
 count=0
 for tail in itertools.combinations(vals[1:],m-1):
  ds={1,*tail};V=[p for p in points if norm(*p) in ds and norm(p[0]-1,p[1]) in ds]
  adj=[sum(1<<j for j,q in enumerate(V) if i!=j and norm(p[0]-q[0],p[1]-q[1]) in ds) for i,p in enumerate(V)]
  C=clique(adj);size=len(C)+2;count+=1
  if size>best[m]:best[m]=size;print(json.dumps({'m':m,'distances':sorted(ds),'size':size,'points':[(0,0),(1,0)]+[V[v] for v in C]}),flush=True)
  if size>({7:16,8:19}[m]):print('COUNTEREXAMPLE');break
 print(json.dumps({'completed_m':m,'alphabets':count,'norm_values':vals,'best':best[m],'scope':'unit segment required; all other norms in listed finite alphabet'}),flush=True)
