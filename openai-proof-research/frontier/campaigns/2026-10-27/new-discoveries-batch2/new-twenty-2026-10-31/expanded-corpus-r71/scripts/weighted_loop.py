import itertools as it,math,json,pathlib,networkx as nx
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];O={}
def save(i,x):O[str(i)]=x;(D/'outputs/weighted-loop.json').write_text(json.dumps(O,indent=2)+'\n');print(i,x,flush=True)
# Every upward-closed nonempty family on [n], n<=5. Optimal family may be assumed upward-closed by monotone closure; this does not increase matching number.
rows=[]
for n in range(1,6):
 ss=list(range(1,1<<n));H=nx.Graph();H.add_nodes_from(ss);H.add_edges_from((a,b) for a,b in it.combinations(ss,2) if a&b not in (a,b));best={s:0 for s in range(2,n+1)};families=0
 for A in it.chain([[]],nx.enumerate_all_cliques(H)):
  families+=1;fam=[x for x in ss if any(x&a==a for a in A)];pack={0:0}
  for a in fam:
   for used,v in list(pack.items()):
    if not used&a:pack[used|a]=max(pack.get(used|a,0),v+1)
  nu=max(pack.values())
  for s in best:
   if nu<s:best[s]=max(best[s],len(fam))
 weights={s:(0,None) for s in best};den=12
 for w in it.combinations_with_replacement(range(den+1),n):
  sz=sum(sum(w[j] for j in range(n) if mask>>j&1)>=den for mask in ss)
  for s in weights:
   if sum(w)<den*s and sz>weights[s][0]:weights[s]=(sz,w)
 rows.append(dict(n=n,upsets=families,optima=best,threshold_witnesses={s:{'size':v[0],'numerators':v[1],'denominator':den} for s,v in weights.items()}))
save(376305,dict(domain='All upward closed families on n=1..5 excluding empty member; enumerate antichains; compare exact maxima to rational threshold witnesses denominator12 and sorted weights in [0,1]',rows=rows))
# Open Temperley-Lieb stochastic generator sum_i(e_i-I), noncrossing link patterns, at most one through-line outside all arches.
def patterns(n):
 out=[]
 def rec(word,up,downs):
  if len(word)==n:
   if up-downs==n%2:
    stack=[];pairs=[-1]*n
    for j,x in enumerate(word):
     if x==1:stack.append(j)
     else:k=stack.pop();pairs[k]=j;pairs[j]=k
    out.append(tuple(pairs))
   return
  if up<(n+1)//2:rec(word+[1],up+1,downs)
  if up>downs:rec(word+[-1],up,downs+1)
 rec([],0,0);return out
def op(p,i):
 j=i+1;a=p[i];b=p[j];q=list(p)
 if a==j:return p
 q[i]=j;q[j]=i
 if a!=-1:q[a]=b
 if b!=-1:q[b]=a
 return tuple(q)
def solve(M):
 N=len(M)
 for c in range(N):
  r=next(j for j in range(c,N) if M[j][c]);M[c],M[r]=M[r],M[c];z=M[c][c];M[c]=[x/z for x in M[c]]
  for j in range(N):
   if j!=c:
    z=M[j][c]
    if z:M[j]=[x-z*y for x,y in zip(M[j],M[c])]
 return [r[-1] for r in M]
def av(n):return (-3)**(n*n)*math.prod(F(3*(2*j-i)+1,2*j-i+2*n+1) for i in range(1,2*n+2) for j in range(1,n+1))
def n8(n):return math.prod(F((3*j+1)*math.factorial(6*j)*math.factorial(2*j),math.factorial(4*j+1)*math.factorial(4*j)) for j in range(n))
rows=[]
for L in range(1,10):
 ps=patterns(L);idx={p:i for i,p in enumerate(ps)};N=len(ps);M=[[F(0) for j in range(N+1)] for i in range(N)]
 for j,p in enumerate(ps):
  for k in range(L-1):M[idx[op(p,k)]][j]+=1;M[j][j]-=1
 M[-1]=[F(1)]*N+[F(1)];v=solve(M);v=[x/min(v) for x in v];assert all(x.denominator==1 for x in v)
 n=(L+1)//2;expected_max=n8(n) if L%2==0 else av(n-1);expected_sum=av(n) if L%2==0 else n8(n)
 rows.append(dict(L=L,states=N,maximum=int(max(v)),sum=int(sum(v)),expected_max=str(expected_max),expected_sum=str(expected_sum),max_equal=max(v)==expected_max,sum_equal=sum(v)==expected_sum))
save(376562,dict(domain='All noncrossing open link states L=1..9; exact Fraction stationary generator calculation. Implementation-to-source TL representation bridge remains diagnostic',rows=rows))
save(376563,dict(domain='Same exact open loop-model enumeration L=1..9',rows=rows))
