import itertools,json,math,collections,sys
from pathlib import Path
L=Path(__file__).resolve().parents[1]
def gamma(k):
 n=3*k+2; E={(1,2),(2,3),(3,4),(4,5),(1,5)}
 E|={(i,i+1) for i in range(5,3*k+2)}
 E|={(v,3*t+2) for v in (1,4) for t in range(2,k+1)}
 E|={(3*s+1,3*(ell+1)+2) for s in range(2,k) for ell in range(s,k)}
 return n,{tuple(sorted((a-1,b-1))) for a,b in E}
def rank(cols):
 basis={}
 for x in cols:
  while x:
   p=x.bit_length()-1
   if p in basis:x^=basis[p]
   else:basis[p]=x;break
 return len(basis)
def betti(faces):
 by=collections.defaultdict(list)
 for f in faces:by[f.bit_count()].append(f)
 ranks={}
 for s in sorted(by):
  if s==0:continue
  ix={f:i for i,f in enumerate(by[s-1])};cols=[]
  for f in by[s]:
   col=0;x=f
   while x:
    b=x&-x;x-=b;col^=1<<ix[f^b]
   cols.append(col)
  ranks[s]=rank(cols)
 return {s-1:len(fs)-ranks.get(s,0)-ranks.get(s+1,0) for s,fs in by.items() if len(fs)-ranks.get(s,0)-ranks.get(s+1,0)}
def edgecheck():
 out=[]
 for k in range(1,9):
  n,E=gamma(k);adj=[0]*n
  for a,b in E:adj[a]|=1<<b;adj[b]|=1<<a
  faces=[0]
  for i in range(n):faces += [f|(1<<i) for f in faces if not f&adj[i]]
  counts=collections.Counter(f.bit_count() for f in faces);d=max(counts);h=[sum((-1)**(j-s)*math.comb(d-s,j-s)*counts[s] for s in range(j+1)) for j in range(d+1)]
  facets=[f for f in faces if all(f>>i&1 or adj[i]&f for i in range(n))]
  row={'k':k,'vertices':n,'edges':len(E),'faces':len(faces),'facet_sizes':sorted(set(f.bit_count() for f in facets)),'h':h,'all_link_F2_sphere':None}
  if k<=5:
   failures=[]
   for f in faces:
    ban=f
    for i in range(n):
     if f>>i&1:ban|=adj[i]
    link=[g for g in faces if not g&ban];b=betti(link);want={d-f.bit_count()-1:1}
    if b!=want:failures.append({'face':f,'betti':b,'expected':want})
   row['all_link_F2_sphere']=not failures;row['links_checked']=len(faces);row['failures']=failures
  out.append(row);print(json.dumps(row),flush=True)
 (L/'outputs/gamma-check.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':edgecheck()
