import numpy as np,json
out=[]
for k in [2,3,4]:
 E=lambda i,j:np.eye(k,dtype=complex)[:,i:i+1]@np.eye(k,dtype=complex)[j:j+1,:]
 D=np.diag(np.arange(1,k+1)); B=np.diag(np.ones(k-1),1)+np.diag(np.ones(k-1),-1)
 hs=[np.sqrt(k)*E(i,i) for i in range(k)]
 for i in range(k):
  for j in range(i):hs += [np.sqrt(k/2)*(E(i,j)+E(j,i)),1j*np.sqrt(k/2)*(E(i,j)-E(j,i))]
 pair=[(h,np.zeros_like(h)) for h in hs]+[(np.zeros_like(h),h) for h in hs]
 tang=np.array([[sum(np.trace(v.conj().T@(1j*(h@d-d@h))).real/k for v,d in zip(vv,[D,B])) for h in hs] for vv in pair])
 u,s,v=np.linalg.svd(tang,full_matrices=True); V=[tuple(sum(u[b,a]*pair[b][r] for b in range(2*k*k)) for r in range(2)) for a in range(k*k-1,2*k*k)]
 W=[]
 for vv in V:
  for b in range(k):
   for c in range(k): W.append(np.concatenate([sum(np.kron(vv[r]@E(i,b),E(c,i)) for i in range(k)).reshape(-1) for r in range(2)]))
 W=np.array(W).T
 gram=W.conj().T@W/(k*k)
 err=np.max(np.abs(gram-np.eye(len(W.T))/k))
 # Commutator acts on first matrix on left, second on right.
 orth=0.
 for vv in V:
  for b in range(k):
   for c in range(k):
    mats=[sum(np.kron(vv[r]@E(i,b),E(c,i)) for i in range(k)) for r in range(2)]
    z=sum(np.kron(d,np.eye(k))@m-m@np.kron(np.eye(k),d) for d,m in zip([D,B],mats))
    orth=max(orth,float(np.linalg.norm(z)))
 assert err<1e-11 and orth<1e-10
 out.append(dict(k=k,normal_dimension=len(W.T),expected=k*k*(k*k+1),gram_error=float(err),adjoint_orbit_error=orth))
print(json.dumps(out,indent=2))
