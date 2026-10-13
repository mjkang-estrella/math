# I242 — complete Crouzeix geometry in base dimension four

**Verdict: the exact-equality part of Q4(r) is proved. No power modulus is claimed.** The result holds for every finite coefficient size and every finite polynomial degree, so it includes the requested degree-at-most-two class. The new inverse step is a rank-one reduction of the complete singular vectors using the original-matrix positive boundary field. It does not amplify scalar nilpotent output rigidity.

All work stayed in the assigned files and primary-excerpt directory. No subordinate agents, live sibling reports, shared edits, staging, commits, publication, research code, tests, numerical experiments, parameter scans, snapshots or seals were used. The supplied count of nine is unchanged pending the parent's independent assessment of this candidate.

## Exact statement

Assume the pinned complete Crouzeix bound and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Theorem E4.** For every integer 1≤n≤4, A∈M_n(C), every finite m≥1 and every M_m-valued polynomial P of finite degree, let

M=max_{z∈W(A)}||P(z)||>0.

If ||P[A]||=2M, then W(A) is a nondegenerate closed disk. In fact there are unit u,v∈C^m for which the scalar polynomial p(z)=v*P(z)u satisfies

||p(A)||=2M=||P[A]||,  max_{W(A)}|p|=M.

There is an irreducible reducing block B of A on which ||p(B)||=2M. If W(A)=a+ρDbar, ρ>0, then p(a+ρz)=Mηz^k for some |η|=1 and integer 1≤k≤deg P.

Consequently, for every 0<r<1, every A∈M_4(C) whose minimum enclosing numerical-range disk is Dbar and with rDbar⊂W(A), and every finite-coefficient-size polynomial P of degree at most two satisfying max_{W(A)}||P||=1 and ||P[A]||=2, one has W(A)=Dbar. This is exactly Q4(r) at ε=0. Neither simplicity of A's spectrum nor an inverse polynomial is assumed.

## Paid proof

The full proof, including the boundary limit, is in [analytic-attempt.md](../experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md). Its main deductions are as follows.

Normalize M=1 and decompose A into irreducible reducing blocks. Some block B has ||P[B]||=2. Its size d is between two and four, and the stipulated bound gives max_{W(B)}||P||=1. Irreducibility implies σ(B)⊂int W(B): a boundary eigenvector is also an adjoint eigenvector and would reduce B.

Choose a fixed maximal singular pair x=vec(X), y=vec(Y) for P[B]. For analytic convex Ω_j shrinking to W(B), put M_j=max_{closure Ω_j}||P|| and F_j=P/M_j. The same pair is maximal for F_j[B], with γ_j=2/M_j→2. The direct proof gives its exact nonnegative identity

E_{X,j}+E_{Y,j}+E_{B,j}+2R_j=2(4/γ_j²−1)a_j²,

where

R_j=3||Y*X||_HS²+∑_{k≥1}||X*b_{k,j}(B)Y||_HS²,

a_j²=∑_{k≥0}||Y*b_{k,j}(B)X||_HS².

A necessary boundary-limit step is supplied, not assumed: normalized exterior maps h_j of convex domains satisfy |h'_j|≤4c_j. Their logarithmic derivatives have a Herglotz probability representation

log(h'_j(z)/c_j)=2∫log(1−ξ/z)dμ_j(ξ).

Under weak convergence of μ_j, the logarithms converge strongly in boundary L² because their Fourier tails are bounded by 4∑_{k>N}k^−2. Exponentiation preserves this convergence. Since σ(B) is strictly interior, the resolvents are uniformly bounded; therefore a_j stays bounded and the original positive fields

H_j=R^ext_j+(R^ext_j)*,  R^ext_j=zh'_j(z)(h_j(z)I−B)^−1

converge strongly in L² to the boundary field H for W(B). The residual identity then gives X*Y=0, all backward moments X*B^kY=0, and zero limiting positive-block slack.

The missing inverse information is its exact matrix form. With D=XX*−YY*, W=[X Y] and J=diag(I,−I),

tr((W*HW)J(W*HW)J)=||H^(1/2)DH^(1/2)||_HS².

Thus ran H is totally isotropic for D almost everywhere. If a support eigenvalue is simple, the resolvent congruence makes rank H=d−1. Because X*Y=0, D has inertia (rank X,rank Y,d−rank X−rank Y). Its maximal isotropic dimension is d−max(rank X,rank Y), forcing rank X=rank Y=1.

Every irreducible B of size at most four has a simple maximal support eigenvalue. Otherwise every pencil value Re(e^−iθB) has multiple largest and smallest eigenvalues. For d≤3 it is scalar. For d=4, centering makes every pencil value square to a scalar; hence its Hermitian generators obey H₀²=aI, K₀²=bI and H₀K₀+K₀H₀=2cI. Removing the H₀ component of K₀ produces two anticommuting generators, unitarily equivalent to two identical 2×2 blocks, contradicting irreducibility. At a simple top eigenvalue λ(θ),

λ+λ''=2∑_{j≠top}|v_j*H'_θv|²/(λ−λ_j)>0,

since equality would produce a common eigenvector of B and B*. Thus a regular analytic boundary arc exists and the rank argument applies on an interval of positive measure.

Write x=ξ⊗u and y=η⊗v. Then p(z)=v*P(z)u has η*p(B)ξ=2 and |p|≤||P||. The scalar bound gives scalar equality. **Only now** use Jin's scalar geometric theorem to obtain W(B)=a+ρDbar. The finite scalar Schur interpolation uniqueness in Jin's Lemma 4 makes p(a+ρz) a polynomial finite Blaschke product, hence ηz^k. Since |p|≤1 on W(A), the full numerical range lies in this same disk. It contains W(B), so it equals the disk. This also proves the asserted scalar witness for A.

The external scalar disk theorem is a named dependency, not claimed as new. Its actual statement and complete Sections 1–8 proof were read and retained. The scalar monomial deduction is also existing mathematics; the new step is obtaining a scalar witness from the complete certificate in dimension four.

## Source contract and the two routes

The actual direct manuscript's `thm:main`, `lem:faber`, `prop:coefficients`, `lem:resolvent`, `thm:domain` and `lem:approx` have exactly the complete finite-size and enclosing-domain scope used. Both product orders FG and GF, the reciprocal coefficient weights, the constant cross coefficient, and the positive-block trace have been retained. Both pinned manuscript hashes match the immutable preprint tree. This is provenance checking, not a truth audit.

The structural companion's `thm:structural`, `thm:representation`, `prop:density`, equality fibers and `lem:comparison` were consulted. Its single normalized positive density represents the **similar** matrix and all coefficient sizes. The direct mass-two field above represents the **original** numerical-range geometry. They are not interchangeable.

The operator-valued maximum/Schur route gives fiberwise isometry identities, but these allow matrix-valued channels and do not alone force a scalar function. The rank reduction supplies the missing bridge. After that bridge, the scalar Schur argument is valid. Neither manuscript already states this dimension-four scalarization or complete disk-rigidity conclusion.

## Active counterexamples and contribution limits

The I238 obstruction remains active. At A=[[0,2],[0,0]] and P(z)=[[0,z],[1,0]], max_{W(A)}||P||=1 and ||P[A]||=2, while P[A] is the irreducible weighted chain (1,2,1). Its unique top right singular vector x has ||P[A]²x||=2, and its scalar square-function sum is 9/4. Thus P[A] need not have a reducing norm-two nilpotent 2×2 block. Its **base** range is the disk, consistent with E4. Here the scalar compression p(z)=z is exactly the witness our conclusion permits.

Adding blocks with numerical ranges inside the same disk preserves equality and prevents a claim that the entire base matrix is a single Jordan block. Constant unitary summands in a matrix Schur function also refute a naive scalar maximum-principle inference from operator-norm saturation. These obstructions are not removed or relabeled as geometric counterexamples.

No actual nondisk exact-equality example exists within the proved E4 class. No assertion is made for all base dimensions, for arbitrary rational witnesses whose poles obstruct the polynomial monomial argument, or for nonattained complete suprema. The proof in fact has ingredients that may extend beyond polynomials, but that extension is not claimed here.

For the positive-deficit Q4(r), no C_r or ε_r is supplied and no exponent is proved. The exact unresolved step is a uniform quantitative version of scalarization across collapsing support gaps and near-reducible blocks, followed by quantitative control of the full numerical range. Inball normalization does not alone bound those intermediate constants. Qualitative compactness or a bare semialgebraic existence statement would not meet the requested standard and is not offered as a substitute.

## Prior art and disposition

Jin proves scalar disk rigidity in all finite dimensions. Åhag–Czyż–Virtanen v3, Section 11, gives scalar polynomial classification and complete disk rigidity through base dimension three. Those primary passages were read. E4 advances the complete geometric conclusion to dimension four and proves scalarization of each attained polynomial equality; it is not the already-known scalar theorem or I238's inverse-conditioned quantitative transport.

A bounded targeted literature search found no matching dimension-four complete scalarization statement. This is not a literature-wide novelty certification. The result is a substantive candidate for independent review under the unchanged standard. It completes the requested exact-equality first target, while leaving the quarter-power stability target open.

Detached SHA-256 values for all five requested artifacts and the fully read primary excerpts are returned with the handoff. Their provenance and exact read extents are recorded in [input-authentication.json](../experiments/i242_crouzeix_four_dimensional_rigidity/input-authentication.json) and [reading-and-failures.md](../experiments/i242_crouzeix_four_dimensional_rigidity/reading-and-failures.md).
