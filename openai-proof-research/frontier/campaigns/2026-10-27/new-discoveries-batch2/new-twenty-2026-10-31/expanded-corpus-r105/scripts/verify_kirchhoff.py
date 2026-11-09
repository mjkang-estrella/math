from fractions import Fraction as F
import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'outputs/kirchhoff-certificate.json').read_text());n=r['n'];I=[[F(i==j)for j in range(n)]for i in range(n)]
def mul(A,B):return [[sum(A[i][k]*B[k][j]for k in range(n))for j in range(n)]for i in range(n)]
def sub(A,B):return [[A[i][j]-B[i][j]for j in range(n)]for i in range(n)]
def parse(A):return [list(map(F,row))for row in A]
E=r['edges'];adj=[[]for _ in range(n)]
for u,v in E:adj[u].append(v);adj[v].append(u)
seen={0};q=[0]
for u in q:
 for v in adj[u]:
  if v not in seen:seen.add(v);q.append(v)
assert len(seen)==n
vout={}
for a,x in r['variants'].items():
 a=int(a);L=parse(x['L']);P=parse(x['P']);G=parse(x['group_inverse']);d=r['degrees'];expected=[[F(sum((F(d[i],d[k])**a)for k in adj[i]))if i==j else -(F(d[i],d[j])**a)if j in adj[i] else F(0)for j in range(n)]for i in range(n)];assert L==expected
 assert mul(L,G)==sub(I,P)==mul(G,L);assert all(sum(row)==0 for row in G);assert mul(P,P)==P
 # Faddeev-LeVerrier computes characteristic coefficients independently of SymPy.
 B=I;coeff=[F(1)]
 for k in range(1,n+1):
  LB=mul(L,B);c=-sum(LB[i][i]for i in range(n))/k;coeff.append(c);B=[[LB[i][j]+(c if i==j else 0)for j in range(n)]for i in range(n)]
 assert list(reversed(coeff))==list(map(F,x['charpoly_coeffs']));assert coeff[-1]==0 and coeff[-2]!=0
 index=-n*coeff[-3]/coeff[-2];assert index==n*sum(G[i][i]for i in range(n))==F(x['spectral_index']);vout[str(a)]=str(index)
assert F(vout['0'])>F(vout['1']);result=dict(verified=True,graph_connected=True,n=n,indices=vout,gap=str(F(vout['0'])-F(vout['1'])),method='Independent Fraction arithmetic; adjacency/degree reconstruction; group-inverse identities; Faddeev-LeVerrier characteristic coefficients. Diagnostic ordinary certificate, not Lean.')
(D/'outputs/kirchhoff-independent-verification.json').write_text(json.dumps(result,indent=2));print(result)
