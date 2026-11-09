import pathlib,json,itertools,math
L=pathlib.Path(__file__).resolve().parent
# Exact labeled graphs through order 3, plus every graph of order 4 versus K2/K3.
def graph(n,m):
 a=[0]*n
 for k,(u,v) in enumerate(itertools.combinations(range(n),2)):
  if m>>k&1:a[u]|=1<<v;a[v]|=1<<u
 return a
def indom(a):
 n=len(a); best=n
 for s in range(1,1<<n):
  if s.bit_count()>=best:continue
  cover=s;ind=True
  for i in range(n):
   if s>>i&1:
    if a[i]&s:ind=False;break
    cover|=a[i]
  if ind and cover==(1<<n)-1:best=s.bit_count()
 return best
def prod(a,b):
 return [sum(1<<(u*len(b)+v) for u in range(len(a)) for v in range(len(b)) if a[i]>>u&1 and b[j]>>v&1) for i in range(len(a)) for j in range(len(b))]
gs=[graph(n,m) for n in range(1,4) for m in range(1<<(n*(n-1)//2))]; cases=[(a,b) for a in gs for b in gs]+[(graph(4,m),graph(n,(1<<(n*(n-1)//2))-1)) for m in range(64) for n in [2,3]]
bad=[]
for a,b in cases:
 z=indom(prod(a,b)); rhs=indom(a)*indom(b)
 if z<rhs:bad.append([a,b,z,rhs])
# Strict subpartitions, matching the source's distinct-parts convention, not ordinary partitions.
def ranks(lam):
 out=[0]*(sum(lam)+1)
 def rec(i,prev,s):
  if i==len(lam):out[s]+=1;return
  for x in range(min(lam[i],prev-1)+1):
   if x==0:out[s]+=1
   else:rec(i+1,x,s+x)
 rec(0,lam[0]+1,0);return out
parts=[]
for a in range(1,19):
 for b in range(1,a+1):
  for t in range(1,a+1):
   if a-(b-1)*t<=0 or t*b<a:continue
   lam=[a-i*t for i in range(b)]; c=ranks(lam); peak=max(range(len(c)),key=lambda i:c[i]); ok=all(c[i]<=c[i+1] for i in range(peak)) and all(c[i]>=c[i+1] for i in range(peak,len(c)-1))
   parts.append({'lambda':lam,'unimodal':ok})
(L/'bounded-checks.json').write_text(json.dumps({'325719':{'executed':len(cases),'counterexamples':bad,'scope':'all labeled graphs through 3 vertices paired; every labeled 4-vertex graph versus K2,K3; finite evidence only'},'325640':{'executed':len(parts),'counterexamples':[x for x in parts if not x['unimodal']],'scope':'distinct subpartitions; a<=18, positive arithmetic progression, t*b>=a; finite evidence only'},'326568':{'executed':'n=9 displayed RHS compared with 9!','rhs':5*44*math.factorial(4)**3,'factorial9':math.factorial(9),'interpretation':'source concerns bipartite tournaments on 18 vertices, not ordinary 9-vertex tournaments; transcription mismatch, zero credit'}},indent=2)+'\n')
print((L/'bounded-checks.json').read_text())
