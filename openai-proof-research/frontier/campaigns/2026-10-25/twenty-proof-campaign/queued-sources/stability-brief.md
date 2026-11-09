# Full Schur-stability counterexample: MathDB370245

Parent-derived simplification of Patel's posted family. Exact source snapshot
370245.json and source HTML stability-2509.06715v1.html; source hash in
stability-source.json. Credit prior posted family; no discovery claim.

Use W=[[0,1],[1/4,3/4]], B=(1/11)[[9,-4],[-4,3]], t=1.
W²=[[1/4,3/4],[3/16,13/16]]>0, W row stochastic.
Stationary left Perron vector pi=(1/5,4/5); pi^T W=pi^T,
pi>0, sums1. W eigenvalues1,-1/4 so Perron eigenvalue1.
B eigenvalues1,1/11, eigenvectors(2,-1),(1,2), respectively;
B positive definite. Form 11*x^T Bx=8*(x1-x2/2)^2+x1^2+x2^2
makes positive-definiteness elementary. rho(B)=1, Be=(5/11,-1/11)<=e,
pi^T Be=1/55>0, and0<t=1<2/rho(B)=2.
I−B=(1/11)[[2,4],[4,8]].
P=W(I−B)=[[4/11,8/11],[7/22,7/11]], eigenvalue1 with vector(8,7).
(I+B)^-1=[[7/12,1/6],[1/6,5/6]].
R=I−W+(I+B)^-1(2W−I)=[[1/2,1/4],[0,1]],
eigenvalue1 with vector(1,2). Thus neither spectral radius is <1.
This avoids irrational eigenvalues and intermediate-value/root estimates.

Complete formal target must include *actual* source matrices, inverse,
positive definiteness of B, primitivity and stochasticity of W,
Perron-vector conditions, rho(B)=1, strict allowed step, both eigenvalues1,
and a formal bridge to failure of Schur stability. Do not count only a
determinant calculation. Standard mathlib spectrum/HasEigenvalue notions
preferred. Can phrase stability as all complex eigenvalues norm<1 if full
finite-dimensional equivalence is documented/proved; best actual
spectralRadius (ENNReal) conclusions using spectrum bound and exactB spectrum.
