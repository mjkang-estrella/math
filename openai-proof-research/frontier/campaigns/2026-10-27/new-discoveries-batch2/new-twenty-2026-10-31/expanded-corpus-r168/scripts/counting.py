import pathlib,json,functools,collections,sys
D=pathlib.Path(__file__).resolve().parents[1];out=[]
if sys.argv[1]=='binary':
 @functools.lru_cache(None)
 def trees(n):
  if n==1:return (None,)
  return tuple((a,b) for i in range(1,n) for a in trees(i) for b in trees(n-i))
 @functools.lru_cache(None)
 def rootmatch(t,p):return p is None or t is not None and rootmatch(t[0],p[0]) and rootmatch(t[1],p[1])
 @functools.lru_cache(None)
 def occ(t,p):return 0 if t is None else int(rootmatch(t,p))+occ(t[0],p)+occ(t[1],p)
 for k in range(2,8):
  groups={};dist=[]
  for p in trees(k):
   signature=[];en=[]
   for n in range(1,10):
    d=collections.Counter(occ(t,p) for t in trees(n));signature.append(d[0]);en.append(sorted(d.items()))
   key=tuple(signature)
   if key in groups and groups[key]!=en:dist.append(repr(p))
   groups[key]=en
  out.append({'pattern_leaves':k,'patterns':len(trees(k)),'host_leaves_range':[1,9],'host_count_total':sum(len(trees(n)) for n in range(1,10)),'bounded_avoidance_signature_groups':len(groups),'strong_signature_discrepancies':dist,'limitation':'coincident finite signatures do not establish Wilf equivalence; this is within source verification, not an extension'})
  (D/'outputs/binary.json').write_text(json.dumps(out,indent=2));print(out[-1],flush=True)
elif sys.argv[1]=='fuss':
 def paths(k,n):
  ans=collections.Counter()
  def rec(x,y,steps):
   if x==n and y==k*n:
    runs=[];c=0
    for a in steps+'N':
     if a=='E':c+=1
     elif c:runs.append(c);c=0
    ans[tuple(sorted(runs,reverse=True))]+=1;return
   if y<k*n:rec(x,y+1,steps+'N')
   if x<n and y>=k*(x+1):rec(x+1,y,steps+'E')
   if x<n and y<k*n and y%k==k-1 and y>k*x and y+1>k*(x+1):rec(x+1,y+1,steps+'D')
  rec(0,0,'');return ans
 def nc(N,k,n):
  ans=collections.Counter();visited=0
  def rec(i,blocks,stack):
   nonlocal visited
   visited+=1
   if i==N+1:
    if blocks[0][-1]!=N:return
    typ=sorted((len(b)-1 for b in blocks if len(b)>1),reverse=True)
    if any(t%(k+1) for t in typ):return
    marked=[blocks[j] for j in range(k+1-1,len(blocks),k+1)] # 1-based (i(k+1)+2): index 1, k+2,... corrected below
    marked=[blocks[j] for j in range(1,len(blocks),k+1)]
    if len(marked)!=n:return
    if any(len(b) not in (1,k+2) for b in marked):return
    size=sum(len(b)==1 for b in marked)
    # infer lambda by removing n-|lambda| arcs of length k+1
    vals=[t//(k+1) for t in typ]
    for _ in range(n-size):
     if 1 not in vals:return
     vals.remove(1)
    if sum(vals)!=size:return
    for t in range(1,len(blocks)//(k+1)+1):
     if sum(len(b)==1 for b in blocks[-t*(k+1):])<t*(k-1)+1:return
    ans[tuple(sorted(vals,reverse=True))]+=1;return
   rec(i+1,blocks+[[i]],stack+[len(blocks)])
   for j,bid in enumerate(stack):
    if blocks[bid][-1]==i-1:continue
    bb=[b[:] for b in blocks];bb[bid].append(i);rec(i+1,bb,stack[:j+1])
  rec(1,[],[]);return ans,visited
 for k,n in [(1,1),(1,2),(1,3),(2,1),(2,2)]:
  a=paths(k,n);b,visited=nc(2*(k+1)*n+1,k,n)
  out.append({'k':k,'n':n,'path_counts':{str(t):v for t,v in a.items()},'partition_counts':{str(t):v for t,v in b.items()},'match':a==b,'sparse_NC_search_nodes':visited,'condition3_scope':'t with t(k+1) <= number of blocks; larger t undefined and not interpreted as correction'})
  (D/'outputs/fuss.json').write_text(json.dumps(out,indent=2));print(out[-1],flush=True)
