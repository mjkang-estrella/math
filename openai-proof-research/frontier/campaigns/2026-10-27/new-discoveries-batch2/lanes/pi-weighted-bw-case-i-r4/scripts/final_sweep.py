import numpy as np
rng = np.random.default_rng(2026)
def ratio(n, X, Y):
    w = np.sort(np.abs(rng.random(n)))[::-1]  # note: w drawn per call is bad; pass w
    raise RuntimeError
def run(n, trials=300, seed=1):
    r = np.random.default_rng(seed)
    w = np.sort(r.random(n))[::-1]*3 + 0.1
    w[0] = w[0]  # descending
    c2 = w[0]**2 + w[1]**2
    worst = 0.0; arg = None
    for t in range(trials):
        kind = t % 5
        if kind == 0:   X = r.normal(size=(n,n))+1j*r.normal(size=(n,n)); Y = r.normal(size=(n,n))+1j*r.normal(size=(n,n))
        elif kind == 1: # near-extremal: top-2 block + small leak
            X = np.zeros((n,n),complex); Y = np.zeros((n,n),complex)
            X[0,1]=1; Y[1,0]=1
            for _ in range(3):
                i,j = r.integers(0,n,2)
                X[i,j] += 0.3*(r.normal()+1j*r.normal())
                Y[i,j] += 0.3*(r.normal()+1j*r.normal())
        elif kind == 2: # wedge-aligned family: X row1 ones, Y col2 ~ w
            X = np.zeros((n,n),complex); Y = np.zeros((n,n),complex)
            X[0,:] = 1; Y[:,1] = w
        elif kind == 3: # diagonal + top-2
            X = np.diag(r.normal(size=n)); Y = r.normal(size=(n,n))+1j*r.normal(size=(n,n))
        else:           # sparse rank-2
            X = np.outer(r.normal(size=n), r.normal(size=n)); Y = np.outer(r.normal(size=n), r.normal(size=n))
        T = X@np.diag(w)@Y - Y@np.diag(w)@X
        lhs = np.sum(np.abs(T)**2)
        xy = np.sum(X*np.conj(Y))
        rhs = c2*(np.sum(np.abs(X)**2)*np.sum(np.abs(Y)**2) - abs(xy)**2)
        rr = lhs/rhs if rhs > 1e-12 else 0.0
        if rr > worst: worst, arg = rr, (kind, t)
    return worst, arg
for n in [6, 8, 12]:
    worst, arg = run(n)
    print(f"n={n}: max ||T||^2 / (c^2||X^Y||^2) = {worst:.6f}   (arg: {arg})")
