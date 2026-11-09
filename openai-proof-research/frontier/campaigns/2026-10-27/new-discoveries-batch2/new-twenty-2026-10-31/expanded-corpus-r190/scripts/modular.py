import pathlib,json,sys,itertools,time,collections
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);p=int(sys.argv[2]);full=(1<<N)-1;edges=set();cover=[set() for _ in range(N)]
for a in range(N):
 for d in range(1,N):
  xs=[(a+j*d)%N for j in range(p)]
  if len(set(xs))==p:edges.add(sum(1<<x for x in xs))
  if all(xs[j]<xs[j+1] for j in range(p-2)) and xs[-1] not in xs[:-1]:cover[xs[-1]].add(sum(1<<x for x in xs[:-1]))
incident=[[] for _ in range(N)]
for e in edges:
 for x in range(N):
  if e>>x&1:incident[x].append(e)
nodes=0;leaves=0;hist=collections.Counter();examples={}
def dfs(pos,A):
 global nodes,leaves
 nodes+=1
 # Every already excluded residue must retain at least one possible covering prefix.
 possible=A | (full ^ ((1<<pos)-1))
 for x in range(pos):
  if not A>>x&1 and not any(c&possible==c for c in cover[x]):return
 if pos==N:
  leaves+=1;s=A.bit_count();hist[s]+=1;examples.setdefault(s,[x for x in range(N) if A>>x&1]);return
 dfs(pos+1,A)
 B=A|(1<<pos)
 if not any(e&B==e for e in incident[pos]):dfs(pos+1,B)
dfs(1,1)
powers={1};z=1
while z<=N:z*=p-1;powers.add(z)
o={'N':N,'p':p,'nodes':nodes,'modular_sets':sum(hist.values()),'cardinalities':dict(hist),'examples':examples,'nonpower_examples':{s:a for s,a in examples.items() if s not in powers},'scope':'All subsets containing 0; distinct-residue modular p-AP freeness, source-ordered prefix coverage. Small composite moduli may have additional repeated-residue AP conventions; no theorem claimed.'}
(D/f'outputs/modular-{p}-{N}.json').write_text(json.dumps(o,indent=2));print(json.dumps(o))
