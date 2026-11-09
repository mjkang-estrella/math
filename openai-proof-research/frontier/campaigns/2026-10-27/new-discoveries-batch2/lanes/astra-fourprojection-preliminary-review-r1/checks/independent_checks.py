"""Independent falsification diagnostics; numerical observations are not proofs."""
from pathlib import Path
import numpy as np, json, sympy as sp
B=Path(__file__).resolve().parents[1];rng=np.random.default_rng(20261028)
def hs(x):return float(np.vdot(x,x).real)
def unitary(n):return np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))[0]
def polar(e):
 if e.shape[1]==0:return e.copy()
 u,s,v=np.linalg.svd(e,full_matrices=False);return u@v
def inverse_sqrt(x,rank):
 if rank==0:return np.zeros_like(x)
 d,w=np.linalg.eigh(x);d=d[-rank:];w=w[:,-rank:]
 assert min(d)>0
 return (w/np.sqrt(d))@w.conj().T
def evaluate(p,q,r,s):
 e=np.column_stack((p,r));f=np.column_stack((q,s));m=e.shape[1];n=f.shape[1]
 P,Q,R,S=[x@x.conj().T for x in [p,q,r,s]]
 u=polar(e);v=polar(f);k=u.conj().T@v
 j=np.diag([1.]*p.shape[1]+[-1.]*r.shape[1]);l=np.diag([1.]*q.shape[1]+[-1.]*s.shape[1]);kp=j@k@l
 a=e.conj().T@e-np.eye(m);b=f.conj().T@f-np.eye(n)
 de,we=np.linalg.eigh(a);df,wf=np.linalg.eigh(b)
 ev=we.conj().T@k@wf;lv=we.conj().T@kp@wf
 rel=np.sqrt(np.maximum(0,(1+de[:,None])*(1+df[None,:])))*ev+np.sqrt(np.maximum(0,(1-de[:,None])*(1-df[None,:])))*lv
 x=inverse_sqrt(P+R,m);y=inverse_sqrt(Q+S,n)
 pp,rr=x@P@x,x@R@x;qq,ss=y@Q@y,y@S@y
 lhs=float(np.trace(P@R+Q@S).real);rhs=float(np.trace(pp@qq+rr@ss).real)
 return dict(lhs=lhs,rhs=rhs,slack=lhs-rhs,bridge=max(np.linalg.norm(x@e-u),np.linalg.norm(y@f-v)),relation=np.linalg.norm(rel),trace_identity=abs(lhs-(hs(a)+hs(b))/2),pinching_identity=abs(rhs-hs((k+kp)/2)),orthogonality=max(np.linalg.norm(P@Q),np.linalg.norm(R@S)),min_gram=min([1.]+list(1+de)+list(1+df)),max_rowcol=max([0.]+list(np.sum(abs(k)**2,axis=0))+list(np.sum(abs(k)**2,axis=1))+list(np.sum(abs(kp)**2,axis=0))+list(np.sum(abs(kp)**2,axis=1))))
patterns=[(0,0,0,0,0),(4,1,1,1,1),(6,2,1,1,2),(8,3,1,2,2),(7,0,2,3,1),(7,2,0,1,3),(6,2,2,0,1),(7,1,3,2,0),(8,4,1,1,2),(5,0,0,2,1)]
rows=[]
for n,a,b,c,d in patterns:
 for repeat in range(100 if n else 1):
  z=unitary(n);w=unitary(n)
  row=evaluate(z[:,:a],z[:,a:a+b],w[:,:c],w[:,c:c+d]);row.update(pattern=[n,a,b,c,d],repeat=repeat);rows.append(row)
# Ill-conditioned but admissible rank-one pairs using a common unitary rotation.
z=unitary(4);gen=z@np.diag([-.9,-.2,.5,1.3])@z.conj().T
d,w=np.linalg.eigh(gen);eye=np.eye(4,dtype=complex);near=[]
for t in [1.,.1,.01,.001,.0001]:
 rot=(w*np.exp(1j*t*d))@w.conj().T
 row=evaluate(eye[:,:1],eye[:,1:2],rot[:,:1],rot[:,1:2]);row['t']=t;near.append(row)
a,b,u,v,x,y=sp.symbols('a b u v x y',real=True)
identities={
'square_difference_positive_ab':sp.expand((1-a*a)*(1-b*b)-(1-a*a-b*b+a*b)**2-(a-b)**2*(1-a*a-b*b)),
'square_difference_negative_ab':sp.expand((1-a*a)*(1-b*b)-(1-a*a-b*b)**2-(a*a+b*b)*(1-a*a-b*b)-(a*b)**2),
'pair_relation_identity':sp.expand((u*u+v*v)*(x+y)**2-(u-v)**2*(x*x+y*y)-2*(u*x+v*y)*(v*x+u*y))}
assert all(z==0 for z in identities.values())
# Independent dense scalar sweep, concentrating additionally near endpoints.
vals=np.unique(np.concatenate([np.linspace(-.999,.999,401),[-1+10.**(-k) for k in range(3,13)],[1-10.**(-k) for k in range(3,13)]]))
aa,bb=np.meshgrid(vals,vals);coef=1-np.sqrt((1-aa*aa)*(1-bb*bb))/(1+aa*bb);slack=aa*aa+bb*bb-coef
summary=dict(random_cases=len(rows),patterns=patterns,min_slack=min(x['slack'] for x in rows),max_bridge=max(x['bridge'] for x in rows),max_relation=max(x['relation'] for x in rows),max_trace_identity=max(x['trace_identity'] for x in rows),max_pinching_identity=max(x['pinching_identity'] for x in rows),max_rowcol=max(x['max_rowcol'] for x in rows),near_singular=near,symbolic_identities={k:str(v) for k,v in identities.items()},scalar_points=len(vals)**2,scalar_min_slack=float(slack.min()),interpretation='No falsifier found. Floating-point checks do not certify the theorem. Near-singular ambient inverse square roots lose accuracy; report all residuals.')
(B/'checks/numerical-cases.json').write_text(json.dumps(rows,indent=2));(B/'checks/independent-results.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))
