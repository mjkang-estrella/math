import pathlib,json,itertools,collections
L=pathlib.Path(__file__).resolve().parents[1]
def det(A):
 A=[r[:]for r in A];n=len(A);den=1;sign=1
 for k in range(n-1):
  p=next((j for j in range(k,n) if A[j][k]),None)
  if p is None:return 0
  if p!=k:A[k],A[p]=A[p],A[k];sign=-sign
  pivot=A[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    num=A[i][j]*pivot-A[i][k]*A[k][j];assert num%den==0;A[i][j]=num//den
   A[i][k]=0
  den=pivot
 return sign*A[-1][-1]
cs=json.loads((L/'outputs/nut-exact-certificates.json').read_text());counts=collections.Counter()
for c in cs:
 A=c['matrix'];assert A==list(map(list,zip(*A)));assert all(sum(abs(x)for x in r)==3 for r in A);assert len({A[i][i]for i in range(8)if abs(A[i][i])==1})<=1
 if 'det'in c:assert c['det']!=0 and det(A)==c['det'];counts['invertible']+=1
 else:
  i=c['zero_principal_minor'];B=[[x for j,x in enumerate(row)if j!=i]for k,row in enumerate(A)if k!=i];assert det(B)==0;counts['zero_principal_minor']+=1
print('PASS',len(cs),dict(counts));(L/'outputs/nut-independent-verification.json').write_text(json.dumps({'certificates':len(cs),'counts':dict(counts),'method':'Independent integer Bareiss elimination; no floating-point matrix screening used in certificate verification.'},indent=2))
