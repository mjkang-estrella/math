import pathlib,json,itertools as it,random
D=pathlib.Path(__file__).resolve().parents[1]
def rank(A,p=1009):
 A=[list(row) for row in A];r=0
 if not A:return 0
 for c in range(len(A[0])):
  j=next((j for j in range(r,len(A)) if A[j][c]%p),None)
  if j is None:continue
  A[r],A[j]=A[j],A[r];v=pow(A[r][c]%p,-1,p);A[r]=[x*v%p for x in A[r]]
  for j in range(r+1,len(A)):
   v=A[j][c]%p
   if v:A[j]=[(x-v*y)%p for x,y in zip(A[j],A[r])]
  r+=1
  if r==len(A):break
 return r
out=[];fail=[];random.seed(79)
# Rank-five binary represented matroids: I5 plus up to three distinct nonzero nonunit columns.
extras=[x for x in range(1,32) if x not in [1,2,4,8,16]]
for m in range(4):
 count=0
 for E in it.combinations(extras,m):
  cols=[1,2,4,8,16]+list(E);n=len(cols)
  def binaryrank(xs):
   B={}
   for x in xs:
    while x:
     j=x.bit_length()
     if j in B:x^=B[j]
     else:B[j]=x;break
   return len(B)
  bases={frozenset(S) for S in it.combinations(range(n),5) if binaryrank([cols[j] for j in S])==5};pairs=list(map(frozenset,it.combinations(range(n),2)));triples=list(map(frozenset,it.combinations(range(n),3)))
  C=[[int(not(a&b) and a|b in bases) for b in triples] for a in pairs];dim=rank(C)
  checks=[]
  for trial in range(3):
   v=[1]*n if trial==0 else [random.randrange(1,20) for _ in range(n)]
   H=[[sum(v[z] for z in range(n) if z not in a|b and a|b|{z} in bases) if not a&b else 0 for b in pairs] for a in pairs];checks.append(rank(H))
  count+=1
  if max(checks)<dim:fail.append({'columns':cols,'catalecticant_rank_mod1009':dim,'HL2_ranks_mod1009':checks})
 out.append({'extra_columns':m,'instances':count,'suspects_so_far':len(fail)})
 (D/'outputs/search-362758.json').write_text(json.dumps({'scope':'all represented binary rank5 matroids with I5 fixed plus 0..3 distinct nonzero nonunit columns (not all matroids); derivative catalecticant and specialized second Hessian rank over F1009, three positive assignments. This is diagnostic only; rank deficiency not exact characteristic-zero refutation.','progress':out,'suspects':fail},indent=2)+'\n')
