import pathlib,json,math,functools
P=pathlib.Path(__file__).resolve().parent
@functools.lru_cache(None)
def tree(p,lctr):
 if not p:return 1
 down=p[1:];right=tuple(x-1 for x in p if x>1)
 moves=([down,right] if lctr else ([down] if down else [])+([right] if right else []))
 return 1+sum(tree(q,lctr) for q in moves)
def partitions(n,m):
 if n==0:yield ();return
 for k in range(min(n,m),0,-1):
  for q in partitions(n-k,k):yield (k,)+q
out=[]
for n in range(1,7):
 best=[0,0];witness=[None,None];cnt=0;sq=[tree((n,)*n,z) for z in [False,True]]
 for p in partitions(n*n,n*n):
  cnt+=1
  for z in [False,True]:
   v=tree(p,z)
   if v>best[z]:best[z]=v;witness[z]=p
 out.append({'n':n,'partitions':cnt,'square_nodes_D_L':sq,'maximum_nodes_D_L':best,'one_maximizer_D_L':witness,'refutation':any(a>b for a,b in zip(best,sq))})
 tree.cache_clear()
(P/'bounded-checks.json').write_text(json.dumps({'355326':out,'scope':'Executed exact recursive move-tree counts, duplicate moves retained as separate histories, n=1..6 only. Not a general proof or novelty clearance.'},indent=2)+'\n');print(json.dumps(out))
