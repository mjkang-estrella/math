# MathDB 348918 diagnostic: Q(n) adjacency A = N N^T - 4I (N = square/line incidence, 6n-2 lines),
# so eigenvalues of A other than -4 are mu-4 for nonzero eigenvalues mu of the small Gram matrix N^T N.
import sys, json, numpy as np
def gram(n):
    lines=[]
    for i in range(n): lines.append([(i,j) for j in range(n)])
    for j in range(n): lines.append([(i,j) for i in range(n)])
    for d in range(-(n-1),n): lines.append([(i,i-d) for i in range(n) if 0<=i-d<n])
    for s in range(0,2*n-1): lines.append([(i,s-i) for i in range(n) if 0<=s-i<n])
    m=len(lines); idx={}
    for li,L in enumerate(lines):
        for sq in L: idx.setdefault(sq,[]).append(li)
    G=np.zeros((m,m))
    for sq,ls in idx.items():
        for a in ls:
            for b in ls: G[a,b]+=1
    return G
def claimed(n):
    if n%2==0: return {n-4:(n-2)//2}
    d={k:1 for k in list(range(-3,(n-11)//2+1))+list(range((n-5)//2,n-4))}; d[n-4]=(n+1)//2; return d
if __name__!="__main__": pass
else:
  lo,hi=int(sys.argv[1]),int(sys.argv[2]); out={}
  for n in range(lo,hi+1):
      G=gram(n); ev=np.linalg.eigvalsh(G); lam=ev-4
      tol=1e-8  # absolute; LAPACK eigvalsh error here is about 1e-12*||G||
      near={}
      for x in lam:
          r=round(x)
          if abs(x-r)<tol and abs(x+4)>0.5: near[r]=near.get(r,0)+1
      # -4 eigenvalue of A: multiplicity n^2 - rank(N) = n^2 - (#nonzero mu)
      nz=int(np.sum(np.abs(ev)>tol)); near[-4]=n*n-nz
      cl=claimed(n); cl[-4]=(n-3)**2
      ok=(near==cl)
      mind=min((abs(x-round(x)) for x in lam if abs(x-round(x))>=tol),default=None)
      out[n]={'ok':ok,'integer_eigs':near if not ok else None,'min_nonint_dist':mind}
      print(n,ok,'' if ok else (near,cl),f'min gap to integer {mind:.3e}',flush=True)
  json.dump(out,open(f'outputs/queens-{lo}-{hi}.json','w'),indent=1)
