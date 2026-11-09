import functools,json,sys
n,m=map(int,sys.argv[1:]);N=n*m;full=(1<<N)-1
black=sum(1<<(i*m+j) for i in range(n) for j in range(m) if (i+j)%2==0);white=full^black
adj=[]
for i in range(n):
 for j in range(m):adj.append(sum(1<<(a*m+b) for a,b in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)] if 0<=a<n and 0<=b<m))
@functools.lru_cache(None)
def go(S,turn):
 if not S:return 0
 color=black if turn==0 else white
 vals=[];moves=S&color
 while moves:
  v=(moves&-moves).bit_length()-1;moves&=moves-1
  R=S&~((1<<v)|adj[v]);score=(S^R).bit_count()*(1 if turn==0 else -1)
  isolated=sum(1<<i for i in range(N) if R>>i&1 and not (adj[i]&R))
  score+=(isolated&black).bit_count()-(isolated&white).bit_count();R&=~isolated
  vals.append(score+go(R,1-turn))
 if not vals:raise ValueError('unexpected isolated position')
 return max(vals) if turn==0 else min(vals)
L=go(full,0);R=go(full,1);print(json.dumps(dict(n=n,m=m,Ls=L,Rs=R,states=go.cache_info().currsize,assertion=L>0>R)))
