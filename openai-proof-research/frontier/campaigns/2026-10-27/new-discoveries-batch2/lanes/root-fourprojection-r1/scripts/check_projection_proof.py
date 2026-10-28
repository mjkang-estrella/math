"""Independent numerical diagnostics of the proof's identities, not a certificate."""
import numpy as np,json
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]
rng=np.random.default_rng(291088)
def power(A,p,eps=1e-10):
 e,v=np.linalg.eigh(A); f=np.zeros_like(e);q=e>eps;f[q]=e[q]**p
 return (v*f)@v.conj().T

def frame(k,n):
 return np.linalg.qr(rng.normal(size=(k,n))+1j*rng.normal(size=(k,n)))[0]
records=[]
for dims in [(7,1,2,3,1),(8,2,3,1,2),(6,0,2,3,0),(8,2,2,2,2),(9,3,1,2,4)]:
 k,p,q,r,s=dims
 worst=dict(source_bridge=0.,grading_identity=0.,spectral_identity=0.,target_identity=0.,deficit=1e10,scalar_min_gap=1e10,gram_min=1.)
 for t in range(20):
  X=frame(k,p+q);Y=frame(k,r+s)
  pf,qf=X[:,:p],X[:,p:];rf,sf=Y[:,:r],Y[:,r:]
  E=np.column_stack((pf,rf));F=np.column_stack((qf,sf))
  G=E.conj().T@E;H=F.conj().T@F
  U=E@power(G,-.5);V=F@power(H,-.5);K=U.conj().T@V
  J=np.diag([1]*p+[-1]*r);L=np.diag([1]*q+[-1]*s);Kp=J@K@L
  A=G-np.eye(p+r);B=H-np.eye(q+s)
  P=pf@pf.conj().T;Q=qf@qf.conj().T;R=rf@rf.conj().T;S=sf@sf.conj().T
  T=power(P+R,-.5);W=power(Q+S,-.5)
  Pp=T@P@T;Rp=T@R@T;Qp=W@Q@W;Sp=W@S@W
  lhs=np.trace(P@R+Q@S).real;rhs=np.trace(Pp@Qp+Rp@Sp).real
  a,Z=np.linalg.eigh(A);b,O=np.linalg.eigh(B)
  kk=Z.conj().T@K@O;ll=Z.conj().T@Kp@O
  uu=np.sqrt(np.maximum(0,(1+a[:,None])*(1+b[None,:])))
  vv=np.sqrt(np.maximum(0,(1-a[:,None])*(1-b[None,:])))
  gap=(a[:,None]**2+b[None,:]**2)*(abs(kk)**2+abs(ll)**2)-abs(kk+ll)**2
  worst['source_bridge']=max(worst['source_bridge'],np.linalg.norm(T@E-U),np.linalg.norm(W@F-V))
  worst['grading_identity']=max(worst['grading_identity'],np.linalg.norm(power(G,.5)@K@power(H,.5)+power(2*np.eye(p+r)-G,.5)@Kp@power(2*np.eye(q+s)-H,.5)))
  worst['spectral_identity']=max(worst['spectral_identity'],np.linalg.norm(uu*kk+vv*ll))
  worst['target_identity']=max(worst['target_identity'],abs(rhs-np.linalg.norm((K+Kp)/2)**2))
  worst['deficit']=min(worst['deficit'],lhs-rhs)
  worst['scalar_min_gap']=min(worst['scalar_min_gap'],gap.min())
  worst['gram_min']=min(worst['gram_min'],np.linalg.eigvalsh(G).min(),np.linalg.eigvalsh(H).min())
 records.append(dict(dims=dims,trials=20,**worst))
(BASE/'proof-diagnostics.json').write_text(json.dumps(records,indent=2));print(json.dumps(records,indent=2))
