import itertools,json,sys,functools
from pathlib import Path
D=Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def classify(rows):
 n=len(rows);k=rows[0].bit_count()
 if all(r==0 for r in rows):return True
 if all(r.bit_count()==k for r in rows) and n==2*k+1 and all(((rows[a]>>b)&1)+((rows[b]>>a)&1)==1 for a in range(n) for b in range(a)):return True
 # Recognize a directed cycle power by candidate successor relation.
 succ=[]
 for v in range(n):succ.append([w for w in range(n) if v!=w and rows[v]&~rows[w]==1<<w])
 def cyc(path):
  if len(path)==n:
   if 0 not in succ[path[-1]]:return False
   return all(rows[path[i]]==sum(1<<path[(i+j)%n] for j in range(1,k+1)) for i in range(n))
  return any(cyc(path+[w]) for w in succ[path[-1]] if w not in path)
 if 2*k<n and cyc([0]):return True
 # General equal-block module partition; enumerate all modules containing 0, then exact-cover modules.
 mods=[]
 for m in range(3,1<<n,2):
  s=m.bit_count()
  if s==n or n%s:continue
  if all((rows[v]&m in (0,m)) and (sum(((rows[u]>>v)&1)<<u for u in range(n) if m>>u&1) in (0,m)) for v in range(n) if not m>>v&1):mods.append(m)
 for m in mods:
  verts=[v for v in range(n) if m>>v&1];base=tuple(sum(((rows[v]>>w)&1)<<j for j,w in enumerate(verts)) for v in verts)
  if not classify(base):continue
  # For Cayley examples, all left translates of a module are supplied by row pattern twin equivalence only in generic recognition.
  # Full equal partitions are expensive; a positive recognizer is enough. Try remaining modules with identical indexed rows up to permutations.
  s=len(verts); candidates=[]
  for b in range(1,1<<n):
   if b.bit_count()!=s or b&m:continue
   if not all(rows[v]&b in (0,b) and sum(((rows[u]>>v)&1)<<u for u in range(n) if b>>u&1) in (0,b) for v in range(n) if not b>>v&1):continue
   vs=[v for v in range(n) if b>>v&1];br=tuple(sum(((rows[v]>>w)&1)<<j for j,w in enumerate(vs)) for v in vs)
   if any(all(base[i]==sum(((br[p[i]]>>p[j])&1)<<j for j in range(s)) for i in range(s)) for p in itertools.permutations(range(s))):candidates.append(b)
  def partition(blocks,used):
   if used==(1<<n)-1:
    reps=[(b&-b).bit_length()-1 for b in blocks]
    qr=tuple(sum(((rows[v]>>w)&1)<<j for j,w in enumerate(reps)) for v in reps)
    return classify(qr)
   v=((~used)&((1<<n)-1));v=v&-v
   return any(partition(blocks+[b],used|b) for b in candidates if b&v and not b&used)
  if partition([m],m):return True
 return False
out=[]
for typ,params in [('C',range(3,14)),('D',range(3,9))]:
 for p in params:
  elems=list(range(p)) if typ=='C' else list(itertools.product(range(p),range(2)))
  n=len(elems);idx={v:i for i,v in enumerate(elems)}
  def mul(a,b):return (a+b)%p if typ=='C' else ((a[0]+(-1)**a[1]*b[0])%p,(a[1]+b[1])%2)
  table=[[idx[mul(a,b)] for b in elems] for a in elems]
  inv=[next(j for j in range(n) if table[i][j]==0) for i in range(n)]
  pairs=[(i,inv[i]) for i in range(1,n) if i<inv[i]];tight=0;unrecognized=[];total=0
  for choices in itertools.product(range(3),repeat=len(pairs)):
   S=[pairs[j][c-1] for j,c in enumerate(choices) if c];total+=1
   sec={table[a][b] for a in S for b in S}-set(S)-{0}
   if len(sec)!=len(S):continue
   tight+=1;rows=tuple(sum(1<<table[v][s] for s in S) for v in range(n))
   if not classify(rows):unrecognized.append(S);print('UNRECOGNIZED',typ,p,S,flush=True)
  print('COMPLETE',typ,p,n,total,tight,len(unrecognized),flush=True);out.append([typ,p,n,total,tight,unrecognized]);(D/'outputs/cayley.json').write_text(json.dumps(out))
