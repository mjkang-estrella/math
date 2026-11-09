# Adversarial diagnostic for Conjecture 9.7 (arXiv 2112.13321). Parameterise a Lorentzian zero-diagonal nonnegative A by
# squares of free variables (rejecting non-Lorentzian), and symmetric X with ||X||_F = 1. Objective (to minimise):
#   f = max_{orderings pi} min(p(lambda_pi), D_1 p(lambda_pi)) / ||A||, subject to X in H(P) (penalised).
# A negative value of f at a feasible point would be a numerical counterexample (to be certified exactly separately).
import numpy as np, itertools, sys, json, time
from scipy.optimize import minimize
seed=int(sys.argv[1]); n=int(sys.argv[2]); BUDGET=float(sys.argv[3]); rng=np.random.default_rng(seed)
iu=np.triu_indices(n,1); m=len(iu[0]); perms=list(itertools.permutations(range(n)))
def unpack(z):
    a=z[:m]**2; A=np.zeros((n,n)); A[iu]=a; A=A+A.T
    Xv=z[m:]; X=np.zeros((n,n)); X[np.triu_indices(n)]=Xv; X=X+X.T-np.diag(np.diag(X))
    X=X/np.linalg.norm(X); A=A/max(np.linalg.norm(A),1e-12); return A,X
def parts(A,X):
    d=np.diag(X); PX=d@A@d-np.sum(A*X*X); DPX=2*np.sum(A@d)
    lam=np.linalg.eigvalsh(X); best=-np.inf
    for pi in perms:
        l=lam[list(pi)]; best=max(best,min(l@A@l,2*np.sum(A@l)))
    return PX,DPX,best
def obj(z):
    A,X=unpack(z); ev=np.linalg.eigvalsh(A)
    pen=10*max(0,ev[-2])  # Lorentzian: second largest eigenvalue <= 0
    PX,DPX,best=parts(A,X)
    return best+10*max(0,-PX)+10*max(0,-DPX)+pen
t=time.time(); runs=0; bestf=(np.inf,None)
while time.time()-t<BUDGET:
    z0=np.concatenate([rng.random(m)+0.1, rng.normal(size=n*(n+1)//2)])
    r=minimize(obj,z0,method='Nelder-Mead',options={'maxiter':4000,'xatol':1e-10,'fatol':1e-12})
    runs+=1
    A,X=unpack(r.x); PX,DPX,best=parts(A,X); ev=np.linalg.eigvalsh(A)
    feas = PX>=-1e-12 and DPX>=-1e-12 and ev[-2]<=1e-12
    if feas and best<bestf[0]: bestf=(best,{'A':A.tolist(),'X':X.tolist(),'P(X)':PX,'D_IP(X)':DPX,'best_margin':best,'A_eigs':ev.tolist()})
print(json.dumps({'n':n,'seed':seed,'runs':runs,'min_feasible_best_margin':bestf[0],'example':bestf[1] if bestf[0]<0 else None,'secs':round(time.time()-t,1)}))
