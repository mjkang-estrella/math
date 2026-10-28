import numpy as np
rng = np.random.default_rng(7)

def check_chain_formula(n, trials=50):
    """T_ij = sum_k w_k (X^Y)_{(ik),(kj)} where (X^Y)_{(ab),(cd)} = X_ab Y_cd - X_cd Y_ab"""
    for t in range(trials):
        w = np.sort(rng.random(n))[::-1]
        X = rng.normal(size=(n,n)) + 1j*rng.normal(size=(n,n))
        Y = rng.normal(size=(n,n)) + 1j*rng.normal(size=(n,n))
        T = X @ np.diag(w) @ Y - Y @ np.diag(w) @ X
        mu = lambda a,b,c,d: X[a,b]*Y[c,d]-X[c,d]*Y[a,b]
        T2 = np.array([[sum(w[k]*mu(i,k,k,j) for k in range(n)) for j in range(n)] for i in range(n)])
        if np.abs(T-T2).max() > 1e-9:
            return False, np.abs(T-T2).max()
    return True, 0.0

def check_Lambda_full_norm(n):
    """Norm of Lambda on FULL wedge^2 HS: columns = basis wedges e_a ^ e_b (a<b HS indices).
       Lambda(e_a^e_b)_{ij} = +w_k if (a,b)=((i,k),(k,j)); -w_k if (b,a)=((i,k),(k,j)); else 0."""
    idx = lambda i,j: i*n+j
    pairs = [(a,b) for a in range(n*n) for b in range(a+1,n*n)]
    N = len(pairs)
    ws = np.sort(rng.random(n))[::-1]
    M = np.zeros((n*n, N), dtype=complex)
    M = np.zeros((n*n, N), dtype=complex)
    for ci,(a,b) in enumerate(pairs):
        ai,aj = divmod(a,n); bi,bj = divmod(b,n)
        if aj==bi:
            k = aj
            M[idx(ai,bj),ci] = ws[k]
        if bj==ai:
            k = bj
            M[idx(bi,aj),ci] = -ws[k]
    lam2 = np.linalg.eigvalsh(M.conj().T @ M)[-1]
    return lam2, (ws.sum())**2, ws[0]**2+ws[1]**2

ok, err = check_chain_formula(4)
print("chain formula T_ij = sum_k w_k (X^Y)_{(ik),(kj)}:", ok, err)
for n in [3,4,5]:
    lam2, s2, c2 = check_Lambda_full_norm(n)
    print(f"n={n}: ||Lambda||^2 on full wedge^2 = {lam2:.4f}; (sum w)^2 = {s2:.4f}; c^2 = w1^2+w2^2 = {c2:.4f}; ratio lam2/c2 = {lam2/c2:.3f}")
