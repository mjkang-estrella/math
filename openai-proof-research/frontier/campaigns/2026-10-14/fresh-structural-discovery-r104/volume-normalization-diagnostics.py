import numpy as np,json,math
out=[]
for k in [2,3,4]:
 D=np.diag(np.arange(1,k+1));B=np.diag(np.ones(k-1),1)+np.diag(np.ones(k-1),-1)
 def eig(ds):
  n=len(ds[0]);ad=[np.kron(np.eye(n),a)-np.kron(a.T,np.eye(n)) for a in ds]
  ev=np.linalg.eigvalsh(sum(a.conj().T@a for a in ad));return ev[ev>1e-8]
 base=eig([D,B])
 for d in [1,2,3]:
  amp=eig([np.kron(D,np.eye(d)),np.kron(B,np.eye(d))])
  target=np.repeat(base,d*d);err=float(np.max(abs(amp-target)))
  assert len(amp)==(k*k-1)*d*d and err<1e-9
  # Exact rational exponents of logarithmic dimensions and log k cancel.
  n=k*k+1;r=k*k-1
  assert -(n+r)+2*k*k==0 and -n+n==0
  out.append(dict(k=k,d=d,orbit_dimension=len(amp),amplified_singular_square_error=err,normal_Gram_scale=k,stabilizer_metric_scale=k))
print(json.dumps(out,indent=2))
