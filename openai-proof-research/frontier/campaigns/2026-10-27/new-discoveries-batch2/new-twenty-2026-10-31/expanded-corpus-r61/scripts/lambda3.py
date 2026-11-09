# Diagnostic search for graphs with lambda_3 = n/3 - 1 not isomorphic to H_{a,b}.
import itertools, numpy as np, sys
def lam3(A): return np.sort(np.linalg.eigvalsh(A))[::-1][2]
def H(a,b):
    w=[a,b,a,b,a,b]; return mult([(i,(i+1)%6) for i in range(6)],w)
def mult(E,w):
    off=np.cumsum([0]+list(w)); n=off[-1]; A=np.zeros((n,n))
    for i,c in enumerate(w):
        A[off[i]:off[i]+c,off[i]:off[i]+c]=1
    for i,j in E:
        A[off[i]:off[i]+w[i],off[j]:off[j]+w[j]]=1; A[off[j]:off[j]+w[j],off[i]:off[i]+w[i]]=1
    np.fill_diagonal(A,0); return A
def sig(A):
    return (tuple(sorted(A.sum(0).astype(int))), tuple(np.round(np.sort(np.linalg.eigvalsh(A)),6)))
Hsig={}
for a in range(0,13):
  for b in range(0,13):
    if a+b==0: continue
    Hsig.setdefault(3*(a+b),set()).add(sig(H(a,b)))
found=[]
# exhaustive n=6
n=6; pairs=list(itertools.combinations(range(n),2))
for m in range(1<<len(pairs)):
    A=np.zeros((n,n))
    for k,(i,j) in enumerate(pairs):
        if m>>k&1: A[i,j]=A[j,i]=1
    if abs(lam3(A)-(n/3-1))<1e-9 and sig(A) not in Hsig[n]: found.append(('n6',m,sig(A)[0]))
print("n=6 non-H hits",len(found),found[:5],flush=True)
# closed vertex multiplications of all base graphs on k<=6 vertices, weights 1..3 (n<=18)
hits=set()
for k in range(2,int(sys.argv[1])+1):
  pk=list(itertools.combinations(range(k),2))
  for m in range(1<<len(pk)):
    E=[pk[t] for t in range(len(pk)) if m>>t&1]
    for w in itertools.product(range(1,4),repeat=k):
      N=sum(w)
      if N%3 or N>18: continue
      A=mult(E,w)
      if abs(lam3(A)-(N/3-1))<1e-9 and sig(A) not in Hsig[N]:
          hits.add((N,sig(A)[0],sig(A)[1]))
print('multiplication non-H hits',len(hits))
for h in sorted(hits)[:20]: print(h[0],h[1],h[2])
