# Numerical diagnostic for Blekherman-Kummer-Sanyal-Shu-Sun Conjecture 9.7 (arXiv 2112.13321): every quadratic homogeneous
# multiaffine stable p(x)=sum_{i!=j} a_ij x_i x_j has the spectral containment property: for every X in H(P),
# P(X)=p(diag X) - sum_{i!=j} a_ij X_ij^2, some ordering lambda of the eigenvalues of X lies in H(p).
# For a degree-2 polynomial hyperbolic w.r.t. e: H = closure{v : q(v) >= 0, D_e q(v) >= 0}.
# Stability of p (nonneg a, symmetric zero-diagonal A): A has exactly one positive eigenvalue (Lorentzian), checked here.
import numpy as np, itertools, sys, json, time
rng=np.random.default_rng(int(sys.argv[1])); n=int(sys.argv[2]); BUDGET=float(sys.argv[3])
def p(A,x): return x@A@x
def Dp(A,x): return 2*np.sum(A@x)    # D_1 p(x) = 2 * 1^T A x
def P(A,X): return np.diag(X)@A@np.diag(X) - np.sum(A*X*X)
def DP(A,X): return 2*np.sum(A@np.diag(X))
def in_H(val,der,tol=1e-12): return val>=-tol and der>=-tol
def margin_best(A,lam):
    best=-np.inf
    for perm in itertools.permutations(range(n)):
        l=lam[list(perm)]; best=max(best,min(p(A,l),Dp(A,l)))
    return best
t=time.time(); tried=0; inH=0; worst=(np.inf,None)
while time.time()-t<BUDGET:
    # random Lorentzian zero-diagonal nonnegative A: rank-one positive part minus PSD part, clipped
    u=rng.random(n); B=rng.normal(size=(n,n)); A=np.outer(u,u)*rng.uniform(0.5,3) - 0.3*rng.random()*(B@B.T)/n
    np.fill_diagonal(A,0); A=np.maximum(A,0); A=(A+A.T)/2
    ev=np.linalg.eigvalsh(A)
    if np.sum(ev>1e-9)!=1: continue
    X=rng.normal(size=(n,n)); X=(X+X.T)/2 + np.diag(rng.normal(size=n)*rng.uniform(0,3))
    tried+=1
    if not in_H(P(A,X),DP(A,X)): continue
    inH+=1
    lam=np.linalg.eigvalsh(X); m=margin_best(A,lam)
    scale=max(1e-12,np.max(np.abs(lam))**2)
    if m/scale<worst[0]: worst=(m/scale,{'A':A.round(6).tolist(),'X':X.round(6).tolist(),'margin':m})
print(json.dumps({'n':n,'seed':int(sys.argv[1]),'samples':tried,'in_H(P)':inH,'worst_normalised_margin':worst[0],'worst_example':worst[1] if worst[0]<1e-3 else None,'secs':round(time.time()-t,1)}))
