import numpy as np,itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for q in [23,19]:
 squares={x*x%q for x in range(1,q)};Q=np.array([[0 if i==j else (1 if (j-i)%q in squares else -1) for j in range(q)] for i in range(q)],dtype=np.int64)
 H=np.ones((q+1,q+1),dtype=np.int64);H[1:,1:]=-Q-np.eye(q,dtype=np.int64)
 if q==19:H=np.kron(np.array([[1,1],[1,-1]]),H)
 n=len(H);assert np.array_equal(H.T@H,n*np.eye(n,dtype=np.int64));np.save(D/f'outputs/H{n}.npy',H)
 B=[]
 for s in range(1,n//2+1):
  A=np.array([[int((i-j)%n in {s,n-s}) for j in range(n)] for i in range(n)],dtype=np.int64);T=H.T@A@H;T-=np.diag(np.diag(T));B.append(T)
 hits=[];tests=0
 subsets=(list(itertools.chain.from_iterable(itertools.combinations(range(len(B)),r) for r in range(len(B)+1))) if n==24 else list(itertools.chain.from_iterable(itertools.combinations(range(len(B)),r) for r in range(4))))
 for inds in subsets:
  tests+=1
  if not inds or not np.any(sum(B[i] for i in inds)):hits.append([i+1 for i in inds])
 row=dict(n=n,paley_q=q,circulant_connection_subsets=tests,diagonalizable_labelled_subsets=hits,scope='fixed displayed Paley/tensor Hadamard; no isomorphism count');out.append(row);print(row,flush=True)
(D/'outputs/hadamard.json').write_text(json.dumps(out,indent=2))
