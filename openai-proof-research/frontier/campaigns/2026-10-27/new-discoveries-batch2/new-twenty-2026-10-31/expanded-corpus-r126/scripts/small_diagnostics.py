import itertools,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
# All labelled racks of prime orders 2 and 3 via permutation-valued left translations.
for n in [2,3]:
 ps=list(itertools.permutations(range(n)));med=[];red=[]
 for ls in itertools.product(ps,repeat=n):
  op=lambda x,y:ls[x][y]
  if not all(op(x,op(y,z))==op(op(x,y),op(x,z)) for x,y,z in itertools.product(range(n),repeat=3)):continue
  if not all(op(op(x,y),op(u,v))==op(op(x,u),op(y,v)) for x,y,u,v in itertools.product(range(n),repeat=4)):continue
  def canonical():
   vals=[]
   for p in ps:
    inv=[p.index(x) for x in range(n)]
    vals.append(tuple(p[op(inv[x],inv[y])] for x in range(n) for y in range(n)))
   return min(vals)
  key=canonical();med.append(key)
  if all(op(op(x,y),z)==op(y,z) for x,y,z in itertools.product(range(n),repeat=3)):red.append(key)
 print('racks',{'n':n,'left_translation_tuples':len(ps)**n,'medial_isotypes':len(set(med)),'2reductive_isotypes':len(set(red)),'difference':len(set(med))-len(set(red))},flush=True)
# Exhaustive two-coloring partitions in selected small Hamming graphs, up to complement.
for q,n in [(2,1),(2,2),(2,3),(3,1),(3,2)]:
 vs=list(itertools.product(range(q),repeat=n));N=len(vs);adj=[[j for j,y in enumerate(vs) if sum(a!=b for a,b in zip(x,y))==1] for x in vs];parameters=set();valid=0
 for mask in range(1,1<<(N-1)):
  colors=[mask>>i&1 for i in range(N)]
  out=[{sum(colors[j]!=colors[i] for j in adj[i]) for i in range(N) if colors[i]==c} for c in [0,1]]
  if all(len(s)==1 for s in out):parameters.add(tuple(next(iter(s)) for s in out));valid+=1
 print('hamming',{'q':q,'n':n,'subsets_up_to_complement':(1<<(N-1))-1,'perfect_colorings':valid,'bc_pairs':sorted(parameters)},flush=True)
# Exact Prouhet moments for all LPs with leading sign fixed through length 20.
# Gray-code updates avoid recomputing the sums for each word.
for n in range(2,21,2):
 powers=[[i**k for k in range(7)] for i in range(n)];mom=[sum(r[k] for r in powers) for k in range(7)];orders=set();sym=set();sign=[1]*n;prev=0
 for t in range(1<<(n-1)):
  if t:
   g=t^(t>>1);bit=(g^prev).bit_length();idx=bit;delta=-2*sign[idx];sign[idx]*=-1
   mom=[x+delta*powers[idx][k] for k,x in enumerate(mom)];prev=g
  order=next((k for k,x in enumerate(mom) if x),7)
  if order:
   orders.add(order)
   if all(sign[i]==(-1)**order*sign[n-1-i] for i in range(n)):sym.add(order)
 print('littlewood',{'n':n,'words':1<<(n-1),'exact_orders_below7':sorted(orders),'symmetric_exact_orders_below7':sorted(sym),'missing':sorted(orders-sym),'limitation':'inside source known m<=8 regime'},flush=True)
