import itertools,pathlib,json
from functools import lru_cache
L=pathlib.Path(__file__).resolve().parents[1]
def refine(A,cells):
 while True:
  new=[]
  for cell in cells:
   buckets={}
   for v in cell:
    key=tuple(sum(A[v][w]for w in c)for c in cells);buckets.setdefault(key,[]).append(v)
   new.extend(tuple(buckets[k])for k in sorted(buckets))
  if new==cells:return new
  cells=new
@lru_cache(None)
def canon(A):
 n=len(A)
 def walk(cells):
  cells=refine(A,cells)
  if all(len(c)==1 for c in cells):
   p=[c[0]for c in cells];return tuple(A[i][j]for i in p for j in p)
  t=next(i for i,c in enumerate(cells)if len(c)>1);cell=cells[t]
  return min(walk(cells[:t]+[(v,),tuple(w for w in cell if w!=v)]+cells[t+1:])for v in cell)
 return walk([tuple(range(n))])
graphs={canon(((0,),))};counts={1:1}
for n in range(2,9):
 nxt=set();trials=0
 for flat in graphs:
  A=[list(flat[i*(n-1):(i+1)*(n-1)])for i in range(n-1)];avail=[i for i,row in enumerate(A)if sum(row)<3]
  for k in range(1,min(3,len(avail))+1):
   for ns in itertools.combinations(avail,k):
    B=tuple(tuple(row+[int(i in ns)])for i,row in enumerate(A))+(tuple(int(i in ns)for i in range(n-1))+(0,),);nxt.add(canon(B));trials+=1
 graphs=nxt;counts[n]=len(graphs);print(n,len(graphs),'augmentations',trials,flush=True)
(L/'outputs/independent-graphs.json').write_text(json.dumps({'counts':counts,'graphs8':[list(g)for g in sorted(graphs)]},indent=2))
# Compare to independent catalogue used in search; completeness is not inferred from counts alone.
def decode(s):
 n=ord(s[0])-63;bits=[(ord(c)-63)>>j&1 for c in s[1:]for j in range(5,-1,-1)];A=[[0]*n for _ in range(n)];k=0
 for j in range(1,n):
  for i in range(j):A[i][j]=A[j][i]=bits[k];k+=1
 return A
catalogue=set()
for s in (L/'sources/graph8.g6').read_text().splitlines():
 A=decode(s)
 if max(map(sum,A))>3:continue
 seen={0}
 while True:
  t=seen|{j for i in seen for j in range(8)if A[i][j]}
  if t==seen:break
  seen=t
 if len(seen)==8:catalogue.add(canon(tuple(map(tuple,A))))
assert catalogue==graphs;print('EXACT CATALOGUE EQUALITY',len(graphs))
