import itertools,pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def parts(n,m=1):
 if n==0:yield ();return
 for x in range(m,min(3,n)+1):
  for r in parts(n-x,x):yield (x,)+r
for n in range(6,9):
 for ps in parts(n):
  group=[]
  for j,p in enumerate(ps):group += [j]*p
  vs=[(1<<i)|(1<<j) for i in range(n) for j in range(i+1,n) if group[i]!=group[j]]
  edges=[e for e in itertools.combinations(range(len(vs)),3) if all(not(vs[i]&vs[j]) for i,j in itertools.combinations(e,2))]
  q=(n-3+1)//2-1;inc=[[] for v in vs]
  for e in edges:
   for v in e:inc[v].append(e)
  colors=[-1]*len(vs);nodes=0
  order=sorted(range(len(vs)),key=lambda v:-len(inc[v]))
  def dfs(pos):
   global nodes
   nodes+=1
   if pos==len(vs):return True
   v=order[pos]
   for c in range(q if pos else 1):
    if any(all(colors[w]==c for w in e if w!=v) for e in inc[v]):continue
    colors[v]=c
    if dfs(pos+1):return True
    colors[v]=-1
   return False
  yes=dfs(0);r={'n':n,'r':3,'k':2,'partition_sizes':ps,'vertices':len(vs),'hyperedges':len(edges),'colors_tested':q,'colorable':yes,'nodes':nodes}
  if yes:r['witness_colors']=colors
  out.append(r);print(r,flush=True);(D/'outputs/kneser.json').write_text(json.dumps(out,indent=2))
