import pathlib,json,collections
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for p,maxn in [(3,8),(4,8),(5,7),(6,6)]:
 for n in range(2,maxn+1):
  powers=[p**d for d in range(n)];N=p**n;dist=[-1]*N;good=bytearray(N);special=set();prefix=0
  for d in range(n):
   prefix+=powers[d]
   for x in range(2,p):special.add(x*prefix)
  dist[0]=0;q=collections.deque([0]);border=bad=0;first=[]
  while q:
   s=q.popleft();v=s;tops=[n]*p;used=0
   for d in range(n):
    peg=v%p;v//=p;used|=1<<peg
    if tops[peg]==n:tops[peg]=d
   if not used&1 and used.bit_count()<=p-2:
    border+=1
    if not good[s]:
     bad+=1
     if len(first)<5:first.append(s)
   for a,d in enumerate(tops):
    if d==n:continue
    for b,e in enumerate(tops):
     if a!=b and e>d:
      t=s+(b-a)*powers[d];v=dist[s]+1
      if dist[t]<0:dist[t]=v;q.append(t)
      if dist[t]==v and (good[s] or t in special):good[t]=1
  assert all(d>=0 for d in dist)
  r=dict(pegs=p,movable_disks=n,states=N,border_vertices=border,border_without_good_shortest_path=bad,first_bad_encoded=first);out.append(r);print(r,flush=True)
(L/'hanoi-results.json').write_text(json.dumps(out,indent=2))
