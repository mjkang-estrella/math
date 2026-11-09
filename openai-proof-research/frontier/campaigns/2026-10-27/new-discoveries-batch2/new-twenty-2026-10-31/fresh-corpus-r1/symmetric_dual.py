from pathlib import Path
import numpy as np,json
from scipy.optimize import minimize,linprog
p=Path(__file__).resolve().parent;a=np.load(p/'selected-packing-forms.npy');m=5;n=6
Q=(a[:,1:n,1:n]+a[:,1:n,1:n].transpose(0,2,1))/2;c=a[:,1:n,n]+a[:,n,1:n];d=a[:,n,n]
def vals(x):return np.einsum('i,kij,j->k',x,Q,x)+c@x+d
r=minimize(lambda v:v[-1],np.r_[np.linspace(.35,.88,5),.65],jac=lambda v:np.r_[np.zeros(5),1.],bounds=[(0,1)]*5+[(0,1)],constraints=[{'type':'ineq','fun':lambda v:v[-1]-vals(v[:5]),'jac':lambda v:np.c_[-2*np.einsum('kij,j->ki',Q,v[:5])-c,np.ones(len(a))]},{'type':'ineq','fun':lambda v:np.diff(v[:5])}],method='SLSQP',options={'ftol':1e-13,'maxiter':400})
x=r.x[:5];v=vals(x);ids=np.where(v>max(v)-1e-7)[0];B=(2*np.einsum('kij,j->ki',Q[ids],x)+c[ids]).T;dual=linprog(np.zeros(len(ids)),A_eq=np.vstack([B,np.ones(len(ids))]),b_eq=np.r_[np.zeros(5),1.],bounds=(0,None),method='highs')
out={'sym_x':x.tolist(),'sym_value':max(v),'active_count':len(ids),'active_ids':ids.tolist(),'weights_success':bool(dual.success),'weights_message':dual.message}
if dual.success:
 w=dual.x;M=np.einsum('k,kij->ij',w,Q[ids]);out.update(weights=w.tolist(),eigenvalues=np.linalg.eigvalsh(M).tolist(),gradient_residual=float(np.max(abs(B@w))))
print(json.dumps(out,indent=2));(p/'symmetric-dual.json').write_text(json.dumps(out,indent=2))
if dual.success:
 def mat(w):return np.einsum('k,kij->ij',w,Q[ids])
 rr=minimize(lambda w:-np.linalg.eigvalsh(mat(w))[0],dual.x,bounds=[(0,1)]*len(ids),constraints=[{'type':'eq','fun':lambda w:np.r_[B@w,sum(w)-1]}],method='SLSQP',options={'maxiter':500,'ftol':1e-10})
 out['psd_weight_attempt']={'success':bool(rr.success),'message':rr.message,'weights':rr.x.tolist(),'eigenvalues':np.linalg.eigvalsh(mat(rr.x)).tolist(),'residual':float(np.max(abs(np.r_[B@rr.x,sum(rr.x)-1])))}
 (p/'symmetric-dual.json').write_text(json.dumps(out,indent=2));print(json.dumps(out['psd_weight_attempt'],indent=2))
