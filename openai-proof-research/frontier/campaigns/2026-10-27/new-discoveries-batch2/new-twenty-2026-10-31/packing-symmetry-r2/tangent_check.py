import numpy as np,json
from pathlib import Path
p=Path(__file__).resolve().parent;old=p.parent/'fresh-corpus-r1'
A=np.load(old/'selected-packing-forms.npy');d=json.loads((old/'symmetric-dual.json').read_text());z=np.r_[0,d['sym_x'],1];ids=d['active_ids'];H=A[ids]+A[ids].transpose(0,2,1)
G=np.einsum('kij,j->ki',H,z)[:,1:6];_,S,V=np.linalg.svd(G[1:]-G[0],full_matrices=True);rank=sum(S>1e-7);N=V[rank:].T;Q=np.einsum('k,kij->ij',d['weights'],H)[1:6,1:6]
print(json.dumps(dict(scope='floating diagnostic only',difference_singular_values=S.tolist(),difference_rank=int(rank),tangent_hessian_eigenvalues=np.linalg.eigvalsh(N.T@Q@N).tolist()),indent=2))
