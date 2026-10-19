# Ellipsoid prefix signing: unfrozen full question

For an arbitrary finite-dimensional real linear map A and any finite sequence u_1,...,u_N in the Euclidean unit ball, the question examined was whether one can choose signs with

    max_(t<=N) ||A sum_(i<=t) epsilon_i u_i||_2 <= C ||A||_HS

for one absolute C, simultaneously for all dimensions, lengths, maps and sequences. No statement was frozen. Neither a full proof nor a full-target counterexample is supplied. An N-dependent, bounded-condition-number or commuting-filter result is not nominated.

## Strongest source and old law

Source097, *The Euclidean Steinitz–Bergstrom theorem*, September24,2026, supplies all-prefix Euclidean signing, together with the much stronger adaptive Dirichlet-energy and filtered-body operations (`assembly.tex`, prop:adaptive, prop:filtered, lem:slab-energy). Its full `matrix.tex` proof includes noncommuting contraction/gain paths; this is not a scalar-only theorem. For diagonal Q in coefficient space,

    R_t R_t^T=I,
    L_t=R_t Q R_t^T=C_t L_(t-1) C_t^T+q_t b_t b_t^T.

The additive trace losses and gains are at most tr Q. Spectral localization and the exact old/new coordinate expansions give the weighted increment estimate. The relative-gain proof uses S=I+Z, V, H=(I+Z+V)^(-1/2)V(I+Z+V)^(-1/2), a polar decomposition and a trace-power comparison; it does not assume Z and V commute. The survival proof combines spectral-scale constraints through Gaussian correlation. Their reconstructed squared state radius sums to O(d).

The actual r44 `prefix-law.md` was read in full after the first ellipsoid feasibility calculation. Its fixed finite set of corrected coefficients simultaneously has hard Euclidean all-prefix support and dimension-free subgaussian marginals for every fixed prefix. It uses the source's energy operation and a classical Gaussian-body/minimax argument. Its optional orthogonal block calculation even controls the whole sign vector. This is a stronger antecedent than the final deterministic source theorem and is credited; it does not assert a subgaussian maximum over all prefixes.

## Strongest compatible primary bound

Kulkarni–Reis–Rothvoss, arXiv:2308.01406v1, Theorems1,2,15,19 and Proposition16, provide fixed-prefix subgaussianity even for an online algorithm against an oblivious sequence. The actual tree body construction, Gaussian-measure estimate, net argument and cloning proof were read. Their all-prefix convex-body conclusion needs Gaussian measure at least 1-1/(2N), rather than a fixed half. This distinction applies directly here; fixed sequence offline signs are within their contract.

For clarity, one can derive the relevant ellipsoid bound without treating a one-coordinate tail as a norm tail. Symmetrize the signing law globally. Its scalar subgaussian bound implies, for an absolute s,

    E exp(<h,Y_t>) <= exp(s^2 ||h||^2/2).

For a standard Gaussian g independent of Y_t, integrate this inequality with h=sqrt(2lambda) A^T g. The Gaussian identity gives

    E exp(lambda ||A Y_t||^2)
      <= det(I-2s^2 lambda A A^T)^(-1/2)

when 2s^2 lambda ||A||_op^2<1. At lambda=1/(4s^2 ||A||_op^2), the logarithm of the right side is at most ||A||_HS^2/(2||A||_op^2), by -log(1-x)<=2x for 0<=x<=1/2. Markov's inequality and a union bound over N yield

    max_t ||A Y_t|| <= C (||A||_HS+||A||_op sqrt(log(2N)))

with positive probability. A=0 is immediate. Separately, project the u_i to the rank(A)-dimensional effective domain and use the pinned Euclidean theorem to obtain C ||A||_op sqrt(rank A). Thus the smaller of these two valid bounds is already available through compatible operations. No lower bound here says the logarithmic term is necessary offline.

## Why replacing d by stable rank in the existing proof is not justified

Conjugating C_t by A produces A C_t A^(-1), which need not be a Euclidean contraction. Inserting a weight A^T A into the original trace budget also fails: weighted trace can increase under an ordinary symmetric contraction. For example let

    A=diag(4,1),  v=(0,1),
    C=[[3/4,1/4],[1/4,3/4]].

C is symmetric with eigenvalues 1 and 1/2 and equals sqrt(I-b b^T) for b=(sqrt(3/8),-sqrt(3/8)). Yet

    ||A C v||^2=25/16 > 1=||A v||^2.

The same strict increase holds for a positive definite L=vv^T+eta I with sufficiently small eta. Thus tr(A C L C^T A^T) is not a monotone contraction potential. The same failure occurs at arbitrarily small innovation size: put C=[[1-a,a],[a,1-a]] for 0<a<1/2 and A=diag(2/sqrt(a),1). Then ||A C v||^2=1+2a+a^2>1, whereas ||b||^2=4a(1-a) tends to zero. Thus a fixed small innovation cap does not repair the weighted trace substitution. These are symmetric rank-one contractions of the assembly type, not arbitrary orthogonal rotations.

The diagnostic refutes only this weighted trace substitution. It is not an obstruction to an anisotropic potential with extra transport terms or to a different signing construction. Such an invariant and its all-length budget were not built. Applying separate Euclidean signings to the spectral bands of A does not give one common signing. The old r4 two-order target and the r44 tree target are different scopes and remain untouched.

The primary terminal ellipsoid balancing theorem surfaced in literature navigation, but its original proof was not acquired/read here; it is not used as a full-prefix premise. Banaszczyk2012 publisher material was navigation only. No literature-exhaustion or priority assertion follows from these searches.
