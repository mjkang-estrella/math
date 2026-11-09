import pathlib,random,math,json,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186'); rng=random.Random(186);p=1009
# Jacobian of (U,V) -> selected entries of UV. Full row rank gives a minor nonzero mod p, hence a nonzero integer polynomial, hence generic dominance in characteristic zero.
def rank(A):
 m=len(A);k=0
 for c in range(len(A[0])):
  pivot=next((i for i in range(k,m) if A[i][c]),None)
  if pivot is None:continue
  A[k],A[pivot]=A[pivot],A[k];inv=pow(A[k][c],-1,p);A[k]=[(x*inv)%p for x in A[k]]
  for i in range(k+1,m):
   a=A[i][c]
   if a:A[i]=[(x-a*y)%p for x,y in zip(A[i],A[k])]
  k+=1
  if k==m:return k
 return k
out=[]
for n in range(int(sys.argv[1]) if len(sys.argv)>1 else 2,(int(sys.argv[2]) if len(sys.argv)>2 else 12)+1):
 for l in range(1,n+1):
  r=n-math.isqrt(n*n-n*l);edges=[(i,j) for i in range(n) for j in range(n) if (j-i)%n>=n-l];best=0
  for trial in range(3):
   U=[[rng.randrange(p) for k in range(r)] for i in range(n)];V=[[rng.randrange(p) for j in range(n)] for k in range(r)]
   A=[]
   for i,j in edges:
    row=[0]*(2*n*r)
    for k in range(r):row[i*r+k]=V[k][j];row[n*r+j*r+k]=U[i][k]
    A.append(row)
   best=max(best,rank(A))
   if best==n*l:break
  rec={'n':n,'l':l,'predicted_rank':r,'jacobian_rank':best,'edges':n*l,'trials':trial+1};out.append(rec);print(json.dumps(rec),flush=True)
(L/('outputs/ranks13-24.json' if len(sys.argv)>1 and sys.argv[1]=='13' else 'outputs/ranks.json')).write_text(json.dumps(out,indent=2))
