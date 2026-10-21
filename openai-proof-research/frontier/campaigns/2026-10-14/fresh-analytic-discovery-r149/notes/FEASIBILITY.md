# Working feasibility, before any freeze

PREFREEZE. One selected Source262 operator family. No nominee or independent grade.

The initial thought of matrix stability was compared with actual I250/I259/I271, I38, r15 P3R, and r30 finite-bubble obstruction. Fixed-profile channel stability and every finite-bubble-budget version are not new targets. P3R's three-well phase asymptotic is preserved and is not pursued. The live feasibility question is full-deficit approximation by an UNRESTRICTED number of rank-one soliton profiles, with arbitrary finite channel dimension, scales, centers, and orientations. No finite budget, fixed eigenvalue cutoff, lowest-eigenvalue-only or approximate-action substitute is offered as the answer. This is not a frozen statement or claimed literature-open problem.

Let sigma=gamma-1/2 in (0,1), p=1+sigma, r=1/sigma, q=r+1, C_gamma=D_sigma/b_sigma. Normalize integral tr W^p=1 and put Delta=C_gamma-Tr(H_W)_-^gamma. For the first N negative eigenvalues -k_i^2, source action/triangular comparison, retaining Young rather than dropping it, yields

 T_N + int[Y(W,A* A)+|A'-BA|_HS^2+c_* Phi_K(A,B)]
 <= b_sigma[Delta+sum_(i>N) k_i^(2 gamma)] + arbitrarily small trial error.

The common spectral shift preserves differences k_l^2-k_i^2. k_1^(2 gamma)<=C_gamma gives a uniform upper kappa, so c_* does not depend on channel dimension, number of rows or smallest binding energy. Source supplies this whole compatible reduction. Its exact-equality proof uses fixed physical dimension to convert operator-norm tails to Hilbert--Schmidt tails; this cannot be silently made uniform in m.

Stronger possibility to test: use trace Young uniform convexity to control W-q(A*A)^r in L^p(S_p), and finite-row Hilbert-valued compactness modulo constant isometries, rather than the fixed-m tail bound. For each fixed N the rank of A*A is <=N, so (tr A*A)^q<=N^(q-1)tr((A*A)^q); this replaces m by N, not by a universal constant. Local H1 compactness can be recovered by approximating finitely many row functions by piecewise constant Hilbert-valued functions and aligning their finite Gram matrices by one isometry. This pays finite-row channel escape without assuming fixed m. It still does not pay unrestricted spectral-tail or multiscale reassembly.

The actual primary FGL2109.05984v2 finite-rank bubble proof is being read, not only its theorem. In its normalized finite-N problem the ground binding energy has a lower bound because the sum of N moments is positive; this supports absence of vanishing. For the full objective, arbitrarily many small eigenvalues may carry all moment mass. Existing r30 explicitly permits this and does not refute unrestricted-cardinality approximation. Need strongest integrated scale-adaptive argument before stating a remaining obligation.

## Stronger integrated route, after primary body reading

Read--Schulz2609.10478v2 Proposition vector-kinetic and its COMPLETE vector/cumulative-mass/quartic-kernel proof supply, at gamma=1, K=pi^2/4 and T_N>=K int tr R_N^3 for any N occupied orthonormal states, independently of the physical channel Hilbert space. This is stronger than treating the moment-tail cutoff as an ultimate obstruction. For ALL negative eigenstates of fixed finite-m W, normalize int tr W^(3/2)=1. With S_N=sum_(j<=N)|lambda_j|, T_N=sum int|psi'_j|^2, R_N=sum psi_j psi_j*, we have T_N+S_N=int tr W R_N and T_N>=K||R_N||_3^3. Holder yields ||R_N||_3<=K^(-1/2) and T_N<=K^(-1/2). Monotone matrix densities and dominated convergence give R_N->R in L3(S3); the full kinetic sum is finite. Therefore EXACTLY

 Delta = [T-K int tr R^3] + [C_1-int tr W R+K int tr R^3].

Both brackets are nonnegative. This retains ALL negative eigenstates even if their number is infinite. It is primary duality/monotone convergence, credited rather than nominated.

Carlen1605.04581v1 Theorem1.1 and its proof (matrix Holder remainder) pay dimension-independent density reconstruction. The matrix result extends to simple matrix fields by weighted block direct sums, then by Lp approximation. For general source Young defect e, s=||Z||_q,
 e = D_sigma-s+s^q + [s-int tr WZ],
 s0=q^(-1/(q-1)), and each summand >=0. For small e, |s-s0|<=C sqrt(e); matrix Holder yields
 ||W-(Z/s)^(q-1)||_p^2 <= 4e/((p-1)s).
Consequently ||W-qZ^r||_Lp(Sp)<=C_p sqrt(e). At gamma1 apply the identical argument with coefficient K to obtain ||W-3K R^2||_(3/2)<=C sqrt(Delta), for Delta sufficiently small. This is compatible with the exact full-density identity. No new substantial operation is being claimed for it.

The full-density route avoids fixing N, but not the scale/channel organization problem. Exact normalized equality examples W_m=w_a I_m, a=(C_1/m)^(1/2), have Delta=0, total occupied L2 mass int tr R=m, and int tr R^3 bounded. Scalar IMS uses the error int |chi'|^2 tr R. There is no universal control of that error on a fixed physical length from the density L3 bound alone: tr R<=m^(2/3)(tr R^3)^(1/3) carries m. The example is ALREADY an exact sum of m solitons, so this diagnoses a localization estimate, NOT a counterexample to unrestricted soliton approximation. An adaptive length of order a^(-1) handles that example. The unpaid issue must therefore be simultaneous adaptation to space, binding scale, and internal subspace, not a bare claim that IMS fails.

For an internal partition V(x)u=(chi_j(x)u)_j with sum chi_j*chi_j=I, the exact kinetic identity has connection A=V*V', A*=-A:
 sum_j |(chi_j u)'|^2 = |u'+A u|^2 + <u,V'^*(I-VV*)V' u>.
For spatial scalar chi_j, A=0. For varying spectral projections it generally does not vanish. Potential splitting is exact only if sum chi_j*Wchi_j=W (true for a complete spectral-projector partition); the new connection still needs payment. A local gauge removes A but rotates the potential. This is ordinary product/Gram algebra, not a new orientation theorem and not a restart of I250--I271.

At finite N, Read--Schulz's exact retained formula is
 T_N-alpha^2/4 int tr R_N^3 = int |U_N'-B_(alpha,N)U_N/2|_HS^2 + (1/4)int G_(alpha,N),
 for 0<alpha<pi. Both right terms are nonnegative by the actual quartic representation. Its excess over the sharp kinetic defect is (pi^2-alpha^2)/4 int tr R_N^3, uniformly bounded independently of N,m. Thus both remainders become small by taking N through the full negative list and alpha up to pi. Merely discarding the primary remainder and saying 'no stability information' would be wrong. What is missing is a uniform conversion of these auxiliary remainders into a spatial/scale/internal partition with summable physical errors and soliton reconstruction. Neither the endpoint-singular tan weight nor eigenvalue-cluster projectors are automatically controlled by a fixed spectral gap. A failed naive route is not evidence of a new result.
