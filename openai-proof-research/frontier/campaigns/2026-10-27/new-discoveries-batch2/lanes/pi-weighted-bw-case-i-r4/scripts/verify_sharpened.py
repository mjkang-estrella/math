import numpy as np
rng=np.random.default_rng(42)

def superopT(X,W):
    n=X.shape[0]; M=np.zeros((n*n,n*n),complex)
    for j in range(n*n):
        E=np.zeros((n,n),complex); E[j%n,j//n]=1
        M[:,j]=(X@W@E-E@W@X).ravel(order='F')
    return M

def min_eig_ratio(X,W):
    n=X.shape[0]; c2=W[0,0]**2+W[1,1]**2
    x=X.ravel(order='F')
    T=superopT(X,W)
    M=c2*np.linalg.norm(X)**2*np.eye(n*n)-c2*np.outer(x,x.conj())-T.conj().T@T
    return np.linalg.eigvalsh(M)[0], c2*np.linalg.norm(X)**2

worst=1e9; worstX=None
for t in range(400):
    n=int(rng.integers(2,7))
    ws=np.sort(rng.uniform(0.1,4,size=n))[::-1]
    W=np.diag(ws)
    kind=rng.integers(0,3)
    if kind==0:
        X=rng.standard_normal((n,n))+1j*rng.standard_normal((n,n))
    elif kind==1:  # structured: few entries
        X=np.zeros((n,n),complex)
        for _ in range(rng.integers(1,4)):
            X[rng.integers(0,n),rng.integers(0,n)]=rng.standard_normal()+1j*rng.standard_normal()
    else:  # near-extremal: top-block supported
        X=np.zeros((n,n),complex); X[:2,:2]=rng.standard_normal((2,2))+1j*rng.standard_normal((2,2))
    m,r=min_eig_ratio(X,W)
    if m<worst: worst=m; worstX=(n,ws,kind)
print("min over 400 random/structured X of min-eigenvalue of [c2||X||^2 I - c2|x><x| - T*T]:", worst)
print("worst case:", worstX)

# also verify original conjecture ratio never exceeds 1 (bilinear alternating max, independent check)
def op_Y(X,W):
    n=X.shape[0]; M=np.zeros((n*n,n*n),complex)
    for j in range(n*n):
        E=np.zeros((n,n),complex); E[j%n,j//n]=1
        M[:,j]=(X@W@E-E@W@X).ravel(order='F')
    return M
mx=0
for t in range(150):
    n=int(rng.integers(2,6))
    ws=np.sort(rng.uniform(0.1,4,size=n))[::-1]
    W=np.diag(ws); c2=ws[0]**2+ws[1]**2
    X=rng.standard_normal((n,n))+1j*rng.standard_normal((n,n))
    sv=np.linalg.svd(op_Y(X,W),compute_uv=False)[0]
    mx=max(mx, sv**2/(c2*np.linalg.norm(X)**2))
print("max ratio ||T_X||^2/(c2||X||^2):",mx)
