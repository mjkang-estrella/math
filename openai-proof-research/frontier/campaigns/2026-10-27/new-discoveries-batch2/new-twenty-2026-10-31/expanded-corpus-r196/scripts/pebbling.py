import pathlib,json,itertools,functools,sys
D=pathlib.Path(__file__).resolve().parents[1]
def comps(s,n):
 if n==1:yield (s,);return
 for k in range(s+1):
  for r in comps(s-k,n-1):yield (k,)+r
rows=[]
for leaves,k,g in [(2,2,2),(2,2,3),(3,2,2),(3,2,3),(2,3,3)]:
 v=2*(leaves+1);target=0;arcs=[]
 for i in range(leaves+1):arcs.append((2*i+1,2*i,g))
 for i in range(1,leaves+1):
  for b in range(2):arcs.append((2*i+b,b,k))
 @functools.lru_cache(None)
 def solv(c):
  if c[target]>0:return True
  for u,w,cost in arcs:
   if c[u]>=cost:
    cc=list(c);cc[u]-=cost;cc[w]+=1
    if solv(tuple(cc)):return True
  return False
 bound=(leaves*k-leaves+1)*g;count=0;bad=None
 for c in comps(bound,v):
  count+=1
  if not solv(c):bad=c;break
 rows.append({'leaves':leaves,'star_weight':k,'G_arrow_weight':g,'p':g,'bound':bound,'configurations_checked':count,'unsolvable':bad,'scope':'first pebbling inequality only; premise follows from source arrow induction, not independently re-proved here'});print(rows[-1],flush=True)
 (D/'outputs/pebbling.json').write_text(json.dumps(rows,indent=2))
