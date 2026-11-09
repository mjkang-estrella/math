# A possible all-deficit interface: partial factors

Author supporting lemma, not a claim that the requisite partial factors exist.

Let X in R^m be centered isotropic. Let A:R^m->R^d have full row rank, d<=m. Suppose a coupling of X with Z in R^d has Z distributed as d independent centered mean-one exponentials and

    E|AX-Z|²<=epsilon².

Then

    inf_(U orthogonal) W2²(Law(X),Law(U(E_m-1)))
       <=4epsilon²+2(m-d).                         (PF)

Proof. Write A=P R, P=(AA*)^(1/2)>0 and R R*=I_d. The random vector RX is centered isotropic in R^d. Apply the parent normalization coupling lemma to P RX and Z to obtain E|RX-Z|²<=4epsilon². Complete the rows of R to an orthogonal matrix [R;R_perp]. On an enlargement of the probability space take a centered product-exponential Z_perp in R^(m-d), independent of (X,Z). Then (Z,Z_perp) is a full product exponential vector and E|R_perp X-Z_perp|²=2(m-d). Add the two orthogonal costs and undo the orthogonal coordinates. This proves(PF).

Thus an all-deficit proof could construct d>=m-Cdelta exponential factors after ANY full-row-rank linear transformation, with total mean-square error O(delta). Bad original covariance directions need not coincide with the source nonlinear normalization's eigenspaces; polar decomposition handles that issue. The statement also works for d=0 with no map/coupling hypothesis, giving the elementary2m bound.

What is not obtained: source Omega_B permits deleting O(delta) eigenvalues outside a fixed neighborhood of1, but this alone does not construct the partial factors or control the transport on the retained subspace. Compressing a noncommuting matrix pencil is not compatible with applying q; mixed blocks may matter. Nor does entropy deficit necessarily decrease under orthogonal marginal projection: Gaussian relative-entropy data processing has the wrong direction for that inference. No moderate-deficit conclusion follows solely from rank counting.
