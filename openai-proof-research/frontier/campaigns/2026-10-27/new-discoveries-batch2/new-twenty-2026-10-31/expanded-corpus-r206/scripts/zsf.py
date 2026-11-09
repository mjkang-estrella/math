import pathlib,itertools,math,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);G=list(itertools.product(range(n),repeat=2));idx={g:i for i,g in enumerate(G)};add=[[idx[((a+c)%n,(b+d)%n)] for c,d in G] for a,b in G];orders=[math.lcm(n//math.gcd(n,a),n//math.gcd(n,b)) for a,b in G];weights=[n//o for o in orders];target=2*sum((p-1)*(n//p) for p in [2,3]) if n==6 else 0
count=0;maxweight=0;hits=[];hist={}
def dfs(start,sums,weight,seq,mixed):
 global count,maxweight
 count+=1;maxweight=max(maxweight,weight);hist[weight]=hist.get(weight,0)+1
 if weight>=target and mixed:
  hits.append({'sequence':[G[x] for x in seq],'weight_numerator':weight});print(json.dumps(hits[-1]),flush=True);raise SystemExit(2)
 for x in range(start,len(G)):
  shifted={add[x][s] for s in sums}
  if 0 in shifted:continue
  dfs(x,sums|shifted,weight+weights[x],seq+[x],mixed or orders[x]==6)
try:dfs(1,{0},0,[],False)
finally:
 rec={'group':'C6^2','nodes_completed':count,'max_cross_numerator_seen':maxweight,'denominator':n,'target':target,'mixed_hits':hits,'hist':hist};(D/'outputs/zsf-C6-square.json').write_text(json.dumps(rec,indent=2));print(json.dumps(rec),flush=True)
