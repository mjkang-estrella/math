import itertools as it,time,json,sys,random
rng=random.Random(8702)
def decomp(seq):
 for c in range(3):
  ab=[i for i in range(3) if i!=c];groups=[{x} for x in set(t[c] for t in seq)]
  while True:
   rect=[(set(t[ab[0]] for t in seq if t[c] in g),set(t[ab[1]] for t in seq if t[c] in g)) for g in groups];merged=False
   for i in range(len(groups)):
    for j in range(i):
     if rect[i][0]&rect[j][0] and rect[i][1]&rect[j][1]:groups[j]|=groups[i];groups.pop(i);merged=True;break
    if merged:break
   if not merged:break
  if len(groups)>1:return True
 return False
# Exact rectangular sweeps; 5 seconds per box, full DFS checks every earlier pair.
for dims in [(2,2,4),(2,3,6),(2,4,8),(3,3,4),(3,4,3),(3,4,6),(4,4,4),(3,5,5),(4,5,5),(6,6,6)]:
 vs=list(it.product(*(range(x) for x in dims)));N=len(vs);succ=[sum(1<<j for j,b in enumerate(vs) if sum(x<y for x,y in zip(a,b))>=2) for a in vs]
 start=time.monotonic();nodes=0;best=[];eq=0;nondec=[];prod=1
 for n in dims:prod*=n
 bound=int(prod**.5);full=True
 def dfs(seq,cand):
  global nodes,best,eq
  nodes+=1
  if nodes%8192==0 and time.monotonic()-start>5:raise TimeoutError
  if len(seq)>len(best):best=seq[:]
  if len(seq)**2==prod:
   eq+=1
   if not decomp([vs[v] for v in seq]):nondec.append(seq[:])
  if not cand:return
  # Search all branches; no optimum pruning: retain all equality witnesses.
  eligible=cand
  while cand:
   bit=cand&-cand;cand-=bit;v=bit.bit_length()-1
   dfs(seq+[v],eligible&succ[v])
 try:dfs([],(1<<N)-1)
 except TimeoutError:full=False
 print(json.dumps(dict(dims=dims,exhaustive=full,nodes=nodes,best_length=len(best),best=[vs[v] for v in best],equality_sequences_checked=eq,indecomposable_equality_witnesses=[[vs[v] for v in seq] for seq in nondec[:5]],seconds=time.monotonic()-start)),flush=True)
