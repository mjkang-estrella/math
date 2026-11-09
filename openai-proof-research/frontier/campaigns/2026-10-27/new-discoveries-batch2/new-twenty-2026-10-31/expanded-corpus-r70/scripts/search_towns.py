import pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1];rows=[];start=time.monotonic()
def clique(vs,k,a):
 adj=[0]*len(vs)
 for i,x in enumerate(vs):
  for j in range(i):
   if (x&vs[j]).bit_count()%k==a:adj[i]|=1<<j;adj[j]|=1<<i
 best=[]
 def expand(P,C):
  nonlocal best
  # greedy proper coloring for upper bounds
  order=[];bounds=[];un=P;color=0
  while un:
   color+=1;avail=un
   while avail:
    bit=avail&-avail;i=bit.bit_length()-1;un^=bit;avail^=bit;avail&=~adj[i];order.append(i);bounds.append(color)
  for z in range(len(order)-1,-1,-1):
   if len(C)+bounds[z]<=len(best):return
   v=order[z];q=P&adj[v]
   if q:expand(q,C+[v])
   elif len(C)+1>len(best):best=C+[v]
   P&=~(1<<v)
 expand((1<<len(vs))-1,[])
 return [vs[i] for i in best]
for n in range(2,12):
 for k in range(2,n+1):
  for a in range(k):
   if n<k+a:continue
   vs=[s for s in range(1<<n) if s.bit_count()%k==a];w=clique(vs,k,a)
   row=dict(n=n,k=k,a=a,maximum=len(w),witness=w,counterexample=len(w)%2==1);rows.append(row)
   print(n,k,a,len(vs),len(w),'COUNTEREXAMPLE' if row['counterexample'] else '',flush=True)
   (D/'outputs/towns.json').write_text(json.dumps(rows,indent=2)+'\n')
   if time.monotonic()-start>100:raise SystemExit('Internal 100 s cap, completed instances saved')
