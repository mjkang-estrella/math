# I82 — measured groups and operator algebras: a finite-row bound and two remaining bridges

Date: 2026-10-10. Premise pin: openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

**Outcome.** Three distinct exact targets were screened. A quantitative finite-row version of the equivariant Gaussian construction is proved below, with one formula working simultaneously for every tracial state and singular covariance. Its row count is polynomial in the supplied Følner-set size, moment cutoff, row bound, and inverse tolerance. Two further targets—ergodic cost interpolation for the particular source group, and abstract nonisomorphism of the particular close C*-algebras—remain unproved and unrefuted. Their failed bridges are tested on the actual actions and algebras.

**Contribution disposition: no substantial finding nominated.** The quantitative result is new to this project, but its proof combines the source's Gaussian square-root normalization and extreme-trace independence with classical regularized functional calculus and noncommutative Lindeberg replacement. A companion already performs row regularization with matrix-size-independent tracial bounds, and Banna–Cébron explicitly describe differentiable-function replacement. The author classifies this as a **technical quantitative theorem**, subject to independent assessment of its precise contract. There is no independent original-proof PASS or contribution PASS in this report. Eight findings remain accepted; the parent alone integrates, reviews, counts, commits, and publishes.

## 1. Scope, prior screens, and exact targets

The rules in AGENTS.md, four current ledgers (README.md, frontier/README.md, frontier/TEN-FINDINGS.md, frontier/iterations/README.md), and I03/I04, I13, I28, and I31 were consulted and snapshotted in the owned source directory. Pertinent spent/parked mechanisms are weighted reflection and infinite annihilator halfspaces in I03/I04; I13's pinning/projection/fluctuation screens; I28's dimension-uniform finite-window Ulam obstruction and filtered no-MCM transfer; and I31's nongradable formal-neighborhood construction. The algebraic geometry is not used here. The earlier structural I07 report was also checked. I80, I81, and I79's in-progress parent wrapper were not used. I76's independent proof passes do not reverse I79's technical contribution verdict supplied in the brief.

All statements and lower proof operations in the pinned corpus are true premises. No apparent inconsistency is used. External literature is comparison evidence, not stipulated truth. These are three targets, not three ways to count one observation:

**Q82: polynomial finite-row invariant trace randomization.** Given commuting invariant orbit rows exactly as in the equivariant source, finite H, a supplied sufficiently invariant finite Følner set F, m≥1 and 0<ε<1, construct from polynomially many rows one unitary V such that

    sup_phi ||alpha_h(V)-V||_(2,phi) < ε       (h in H),
    sup_phi |phi(V^ell)| < ε                  (1≤ell≤m).

The suprema range over all tracial states of the generated row algebra, not just ambient limit traces or action-invariant traces. The polynomial must be uniform over the algebra, action, covariance, trace, and number of tested h, once |F| is paid. This is proved in §§3–7. It strengthens a lower operation quantitatively, not an absorption characterization.

**C82: ergodic cost interpolation.** For the specific Γ and η in §8, does every real 1<c<1+η occur as the cost of an essentially free **ergodic** pmp action of that same Γ on a standard probability space? No soficity, exactness, residual finiteness, or free-product preservation is assumed. The source gives high and arbitrarily low costs of specified actions, not an interval theorem. We verify ergodicity of its finite-height actions; invariant mixtures fail the target's ergodicity. C82 remains open here.

**A82: abstract nonisomorphism.** For each sufficiently small t>0 take exactly D=D_t and P_0,P_t from the close-separable source. Are E_D(P_0) and E_D(P_t) nonisomorphic as abstract unital C*-algebras? The source excludes spatial conjugacy in its given representation. Section 9 gives an exact Aut(D) criterion and the missing passage from spatial normalizers to arbitrary automorphisms. A82 remains open here; no obstruction to arbitrary homomorphisms is asserted.

## 2. Source contracts and paid lower operations

Exact paths, labels, statement blocks, Git/SHA-256 identities and bound passages are retained in source-contracts.json, passages.json, and selected-domain.json. Paths below are beneath preprints/ at the pin.

1. **Strong-Ulam-Stability-Characterizes-Amenability-October-5-2026**, build/strong-ulam-stability.tex, thm:main and eq:distance-goal: countable G is strongly Ulam stable iff amenable. Defect is the supremum over all pairs g,h in operator norm; the correcting representation acts on the same arbitrary complex Hilbert space. Every nonamenable countable G and δ>0 admits a separable-space witness with defect<δ and distance>1/10 from every representation. Its prescribed-subspace transfer, truncation, comparison circuits and signed-frame obstruction (lem:priority, lem:truncate, prop:comparison, lem:witness) already have dimension-independent finite-block estimates. Finite blocks at all group locations do not make the Hilbert space finite dimensional. Global operator norm cannot be replaced by finite windows or normalized 2-norm.
2. **Unitarizability-Implies-Amenability-for-Countable-Groups-September-23-2026**, introduction and conclusion: the stronger witness is a genuine nonunitarizable representation with uniform bound≤1+ε for every ε>0, separably acting when G is countable. Direct-sum kernel-energy obstruction and subgroup induction are paid operations; the conclusion also treats arbitrary discrete groups with possibly nonseparable induced witnesses. Its group-ring extension consequence is already explicit and excluded from discovery. Finite sparse construction parameters depend on the contracting average of G.
3. **Equivariant-Jiang-Su-Stability-for-Amenable-Actions-in-the-Unital-Stably-Finite-Case-October-5-2026**, introduction thm:main: A is simple, separable, unital, infinite dimensional, nuclear, stably finite and Z-stable; G is countable discrete amenable; α is any action. It is cocycle conjugate to α⊗id_Z. This actual statement has **no** outerness, UCT, trace-boundary or trace-orbit hypothesis. We neither add one nor extend to nonunital/nonnuclear cases. In rows.tex, prop:rows provides commuting invariant orbit algebras C_i and bounded self-adjoint x_(i,g), centered and variance one at every trace. Lemma factor-independence gives independence at every extreme trace of C=C*(union C_i), including traces not extending to the ambient algebra. Proposition joint-clt already has uniform fixed-word moment error estimates for nonidentically distributed rows.
4. In that paper's gaussian.tex, the square-root trace bound, Gaussian quadratic formula, and Steps 1–5 of prop:uniform-unitaries handle singular covariance and compare F,hF on the same Gaussian realization. A polynomial p(0)=0 approximates sqrt(s) to η/sqrt(|F|). Its empirical prescription is self-adjointized; the symmetrized empirical covariance need **not** be positive. Moment determinacy and finite-covariance compactness give a common sufficiently large N, without a numerical row bound. Splittings.tex already supplies weighted Haar distribution, equal-trace projections, two coordinate selections and absorption. Those consequences are not counted again.
5. **Cuntz-comparison-and-Jiang-Su-absorption-September-23-2026**, sections/tracial.tex, tr:lipschitz and tr:regularized-overlap: W(1+W*W)^(-1/2) is controlled by tracial functional calculus and resolvents without the old norm of W or a matrix-size constant. Positive Gram regularization is therefore already a lower operation. Q82's additional obligation is coupling it to the changing scalar covariance, Fourier tests, and simultaneous translations with an explicit row budget.
6. **Close-Separable-Cstar-Algebras-Without-Spatial-Conjugacy-October-5-2026**, build/main.tex, prop:sequences, lem:invariant, lem:ambient, lem:bad-inclusion: arbitrarily close unital norm-separable A,B on separable H have A''=B'' without spatial conjugacy. The input P_0,P_t themselves are conjugate by a small unitary that need not normalize D. The relative product/spatial tensor-norm test and simultaneous normalizer limit, including the mt versus 2sqrt(m) witness for m>4/t², are already proved. Abstract nonisomorphism is not a source conclusion.
7. **Near-Inclusions-of-von-Neumann-Algebras-Without-Small-Spatial-Embeddings-October-5-2026**, introduction, near.tex and obstruction.tex: one-sided approximants in N need not be contractive. Gap tends to zero but every spatial embedding has displacement bounded away from zero; embeddings do exist. Entire-unit-ball Fourier estimates, projection/corner corrections and clock-shift winding are paid operations. **Universal-strong-Kadison-Kastler-stability-September-23-2026**, thm:main, requires two-sided unit-ball distance and gives a universal qualitative modulus independent of type and representation. Its UCP perturbation and modular-alignment operations do not convert a one-sided hypothesis into a two-sided one. Neither companion settles A82.
8. Section 8 states the cost contract and actual relative compression, finite-model rank transfer, and height propagation. Merely changing M is not a discovery.

External comparisons use actual retained primary bytes. Burger–Ozawa–Thom, arXiv:1010.0565v1, Theorems 3.1–3.2, already give global amenable stability with δ+120δ² for δ≤1/10 and amenable-subgroup correction; no relative-averaging relabeling of I28 is fresh. Szabó–Wouters, published Analysis & PDE 18 (2025), Corollary C and stronger Theorem 5.7, compare equivariant uniform Gamma and absorption. Banna–Cébron, Operator-Valued Matrices with Free or Exchangeable Entries, both the author-hosted 2018 body and the currently observed arXiv v3 (2022), Theorem 3.1, its proof and Remark 3.2 explicitly give telescoping replacement and its differentiable-function extension. Their free/exchangeable distribution theorems are not applied to tensor-independent rows: the needed estimate is proved below. Version pages and responses are retained; the author-hosted body is identified by its bytes rather than silently equated with the latest arXiv version.

## 3. Q82: exact theorem and construction

Let C be a unital C*-algebra with nonempty T(C), generated by pairwise commuting unital subalgebras C_i (i≥1). Let G act by α. Suppose self-adjoint x_(i,g)∈C_i satisfy, for one M≥1,

    ||x_(i,g)||≤M,
    phi(x_(i,g))=0, phi(x_(i,g)^2)=1        (phi∈T(C)),
    alpha_h(x_(i,g))=x_(i,hg).

The C_i can be the source's invariant orbit algebras. Different rows need not have identical joint distributions. Distinct rows factor at every extreme trace, by the stipulated factor-independence lemma under the generation and commutation hypotheses.

**Theorem Q.** Fix 0<ε<1, m≥1, finite H⊂G and nonempty finite F⊂G of size n satisfying

    |hF △ F|/n ≤ δ := ε^6/2^20       (h∈H).

Set

    t=16 ε^(-2), r=ε^6/(2^24 n),
    N=ceil(2^200 M^12 m^6 n^9 ε^(-32)).                 (3.1)

There is a specific V∈C*(C_1,…,C_N) satisfying both Q82 tests, with the same N for all traces and h∈H. No covariance nonsingularity, invariant traces or |H| bound is required. Amenability only supplies F; a supplied F in any group suffices.

For E=F or hF index matrices by E and define

    z_g=N^(-1/2)sum_i x_(i,g),
    K_E=((nN)^(-1)sum_i x_(i,g)x_(i,k))_(g,k∈E),
    Z_E=(z_g/sqrt(n))_(g∈E),
    f_r(s)=(s+r)^(-1/2), h_r(s)=s(s+r)^(-1/2),
    Q_E=Z_E* f_r(K_E) Z_E - Tr_E h_r(K_E),
    V=exp(i t Q_F).                                     (3.2)

Tr_E is the **unnormalized algebra-valued diagonal sum**. K_E is positive: it is the average of Gram matrices X_i*X_i/n, where X_i=(x_(i,g))_g is a row. It is the unsymmetrized covariance; its entries need not be self-adjoint, but the matrix is. Q_E is self-adjoint. Functional calculus in M_n(C) works also at zero because r>0. Reordering E merely conjugates by a scalar permutation matrix. Relabeling gives exactly

    alpha_h(Q_F)=Q_(hF).                                (3.3)

The prescription is trace-independent and uses the same rows for every E. Individual ||Q_E|| may grow with N; V always has norm one.

For source A, these elements lie in A^ω∩A'. Weighting a limit trace τ by any positive a∈A gives a tracial functional on C, so the same unitary satisfies |τ(aV^ell)|<ετ(a) when τ(a)>0, and zero when τ(a)=0. This is the already-paid weighting operation. Formula (3.1) counts **rows in the ultrapower**, not coordinate lifts. It is not an effective cocycle-conjugacy algorithm or a uniform rate for a finite set of original elements of A.

## 4. Constructive approach I: quantify the polynomial prescription

For D≥1 use the actual Bernstein polynomial

    p_D(s)=sum_(k=0)^D sqrt(k/D) binom(D,k)s^k(1-s)^(D-k).

It vanishes at zero. For B binomial(D,s), p_D(s)=E sqrt(B/D). The square-root Hölder inequality, Jensen and Var(B/D)≤1/(4D) give

    sup_[0,1]|p_D(s)-sqrt(s)|≤(4D)^(-1/4).

Hence D≥n²/(4η⁴), enlarged for strict inequality, pays the source's η/sqrt(n) error. Its monomial coefficient l1 norm is at most 3^D: expand (1-s)^(D-k), sum absolute coefficients as 2^(D-k), and sum the binomial terms. This is an upper envelope, not a lower bound on all approximants.

The source's row-partition argument makes each fixed ordered polynomial moment effective, with constants bounded by Bell(d+r)M^d(2M²)^r for d fluctuation and r centered-covariance factors. Nonsingleton partitions give O(N^-1/2); pair collisions give O(N^-1). Substitution into powers of a degree-D prescription grows these constants with D and the coefficient norm. Fourier approximation on a bounded interval additionally pays tail moments and another degree. This supplies finite computable bounds after parameter choices but does **not** yield (3.1) from these estimates. It neither disproves Q82 nor proves an exponential complexity lower bound.

A separate sample-splitting repair was rejected. One block estimating covariance and an independent block forming z need not have the same covariance: the rows are not identically distributed. In actual matrix rows, x_1=Z⊗I, x_2=Z⊗X have off-diagonal covariance zero, whereas x_1=x_2=Z⊗I have covariance one, all centered variance-one contractions. Independence does not identify these matrices. The successful construction uses the same rows and pays their dependence by Hölder.

## 5. Constructive approach II: positive covariance regularization

Fix an extreme trace φ and work in its tracial GNS von Neumann algebra. Write ||·||_p for Lp norms; for matrices use Tr⊗φ, **without** dividing by matrix size. Rectangular matrices are embedded in a larger square algebra with the same convention. Independence is at this trace. Comparison matrices may depend on φ, while (3.2) does not.

For finite J containing F and all hF set

    R_(g,k)=N^(-1)sum_i phi(x_(i,g)x_(i,k)), S_E=R|_E/n.

Traciality makes R real symmetric, positivity makes it positive semidefinite, and its diagonal is one. Thus S_E≥0 and Tr S_E=1. Define

    Q_E^0=Z_E* f_r(S_E) Z_E - Tr h_r(S_E).                (5.1)

The last term is a scalar. The following bounds are uniform in φ:

    ||z_g||_8≤8M,
    ||K_E-S_E||_4≤4nM²/sqrt(N),
    ||K_E-S_E||_2≤4nM²/sqrt(N),
    ||Z_E||_8≤8sqrt(n)M.                                 (5.2)

For the first, expand φ(z_g^8). Independence and centering kill singleton rows. At most Bell(8)≤8^8 partitions remain, using at most four row labels. N^-4 cancels their at-most N^4 choices; each expectation has modulus≤M^8. For a covariance entry center **each individual row** as y_i=x_(i,g)x_(i,k)−φ(x_(i,g)x_(i,k))1, of norm≤2M². Its fourth-moment expansion (with alternating adjoints) has three pair partitions and one four-block partition, giving at most 4(2M²)^4/N². Its L4 norm is consequently≤4M²/sqrt(N). The degree-two calculation gives the asserted L2 bound. Sum the n² matrix entries after division by n. Summing n column entries after division by sqrt(n) gives the last bound. No normalized/unnormalized trace conversion is hidden.

For positive B,D and p≥1, regularized functional calculus gives

    ||f_r(B)-f_r(D)||_p≤(1/2)r^(-3/2)||B-D||_p,
    ||h_r(B)-h_r(D)||_p≤r^(-1/2)||B-D||_p.               (5.3)

Indeed

    (B+r)^(-1/2)=pi^(-1)int_0^infty
                        u^(-1/2)(B+r+u)^(-1)du.

Subtract and apply the resolvent identity, with both resolvent norms≤(r+u)^(-1). The integral constant is (1/2)r^-3/2. The square-root difference formula uses u^(1/2) and has constant (1/2)r^-1/2. Now h_r(B)=(B+r)^(1/2)−r(B+r)^(-1/2); the second bound follows. All difference integrals converge. These are standard estimates, consistent with the companion's regularization operation.

Hölder with exponents 8,4,8 and ||Tr_E T||_2≤sqrt(n)||T||_2 give, for 0<r≤1,

    ||Q_E-Q_E^0||_2
      ≤[128n²M⁴r^(-3/2)+4n^(3/2)M²r^(-1/2)]/sqrt(N)
      ≤200n²M⁴r^(-3/2)/sqrt(N).                          (5.4)

Thus correlation between K_E and Z_E is explicitly paid. Replacing an empirical covariance by its mean inside a quadratic without (5.4) would not be justified.

## 6. Two finite-row Gaussian comparisons

### 6.1 Rowwise characteristic-function replacement

For a finite index set J let A=(a_(g,k)) be real symmetric, L=sum|a_(g,k)|, and use the unnormalized coordinate column z=(z_g). Set Q=z*Az−Tr(AR). For a real centered Gaussian ξ with covariance R put q=ξ^T Aξ−Tr(AR). Then

    |phi(exp(i s Q))−E exp(i s q)|
      ≤10^9(1+|s|)^3(1+L)^3M^6/sqrt(N).                 (6.1)

This permits noncommuting coordinates within a row and nonidentical row distributions.

**Proof.** For each i let y_i be an independent classical Gaussian row with covariance R_i=(φ(x_(i,g)x_(i,k))), independent also of every original row. R_i is real positive semidefinite with diagonal one. Replace rows one at a time in the enlarged tensor tracial probability space. One can equivalently use the tensor product of row GNS spaces: product independence identifies all original joint moments and hence continuous functional calculus of each bounded original polynomial.

At one replacement let Z_g be the normalized sum of the other current rows. Scaling the selected row by u∈[0,1] gives a self-adjoint quadratic

    X(u)=B+uD+u²E,
    D=N^(-1/2)sum a_(g,k)(Z_g y_k+y_g Z_k),
    E=N^(-1)sum a_(g,k)y_g y_k.

The constant centering is included in B. The same formula with x replaces the original selected row. Every coordinate of a Gaussian or original row has Lp norm≤6M for p≤6. Nonsingleton partitions of six factors therefore give ||Z_g||_6≤36M, uniformly in the replaced-row count. Hölder yields

    ||D||_3≤432LM²/sqrt(N), ||E||_3≤36LM²/N,
    ||D+2uE||_3≤504LM²/sqrt(N).                          (6.2)

The L2 bounds follow because the scalar trace is a probability trace.

For F(u)=trace(exp(i s X(u))), three Duhamel differentiations and tracial Hölder give

    |F'''(u)|≤|s|³||D+2uE||_3³
                   +6|s|²||D+2uE||_2||E||_2.            (6.3)

There are six ordered-simplex terms involving three X' factors, each simplex having volume 1/6, and the three placements of X''=2E in the two-factor terms. X'''=0. Exponential factors are unitary; no ||B|| factor enters. Gaussian coordinates can be treated pointwise: for each finite scalar realization, all remaining operators are bounded and Duhamel applies. Bounds (6.2) give integrable domination for differentiation and integration. No Gaussian operator-norm cap is used.

The traces of the zeroth, first and second Taylor coefficients at u=0 agree for the selected original and Gaussian row. Each term contains at most two selected-row factors. These commute with all remaining rows and the exponential factors from B, so their expectations reduce to the matching first and second row moments by product independence. The argument replaces an entire row; replacing one coordinate while keeping noncommuting coordinates of the same row in B would not justify this cancellation.

Taylor's integral remainder and (6.2)–(6.3) bound a single replacement by

    10^9(1+|s|)^3(1+L)^3M^6 N^(-3/2).

The constant is deliberately loose: 504³+6·504·36<1.3·10^8 and each of the two remainders has factor 1/6. Summing N replacements proves (6.1). The final normalized Gaussian sum has covariance N^-1sum R_i=R. This implements the standard Lindeberg operation, not a claimed invention of it. ∎

For (5.1) use A=f_r(S_E)/n, so each entry is bounded by r^-1/2/n and L≤n r^-1/2. Tracial Duhamel and (5.4) yield

    |phi(exp(i s Q_E))−E exp(i s q_E)|
      ≤[200|s|n²M⁴r^(-3/2)
        +10^9(1+|s|)^3(1+n r^(-1/2))^3M^6]/sqrt(N).     (6.4)

### 6.2 Translated second moments on the same realization

The row-partition calculation for any four indices gives

    |phi(z_a z_b z_c z_d)
      −R_ab R_cd−R_ac R_bd−R_ad R_bc|≤4M⁴/N.             (6.5)

The single four-block term costs M⁴/N; for each of three pairings dropping the distinct-row restriction costs at most M⁴/N. Second moments are R exactly. Thus squared L2 norms of centered quadratic forms differ from their Gaussian counterparts by at most 4M⁴ times the squared coefficient l1 norm, divided by N.

Apply this to Q_(hF)^0−Q_F^0 with coefficients embedded in J. Its coefficient l1 norm is≤2n r^-1/2. Both Gaussian forms use the **same** Gaussian vector with covariance R on J. Taking square roots gives an error≤4nM²r^-1/2/sqrt(N). Apply (5.4) twice to obtain

    ||Q_(hF)−Q_F||_(2,phi)
      ≤||q_(hF)−q_F||_(L2)
                      +500n²M⁴r^(-3/2)/sqrt(N).          (6.6)

No translation invariance of R is needed. Independent copies cannot replace these same-realization forms.

## 7. Gaussian normalization and the constant budget

Take unit Gram vectors v_g for R on J and a single standard Gaussian W on their span. Define

    P_E=n^(-1)sum_(g∈E)v_g v_g^T,
    B_E=P_E(P_E+r)^(-1/2),
    q_E=<W,B_E W>−Tr(B_E).

Nonzero eigenvalues of P_E equal those of S_E. To check this comparison at the level of the quadratic, let T have columns v_g/sqrt(n); then S_E=T*T, P_E=TT* and T f_r(T*T)T*=P_E f_r(P_E). Thus q_E is exactly the Gaussian comparison used in §6. We have Tr P_E=1 and rank≤n. For its positive eigenvalues λ,

    ||B_E||_HS²=sum λ²/(λ+r)≥1−nr,
    ||B_E−sqrt(P_E)||_HS²≤nr.                            (7.1)

The first estimate uses λ−λ²/(λ+r)=λr/(λ+r)≤r. For the second use (a−b)²≤a²−b² when 0≤b≤a, with a=sqrt(λ), b=λ/sqrt(λ+r). Both functions vanish at zero. No unregularized covariance inverse is taken.

The source's square-root trace inequality, cancellation on F∩hF, and (7.1) imply

    ||B_(hF)−B_F||_HS≤sqrt(δ)+2sqrt(nr),
    ||q_(hF)−q_F||_(L2)≤sqrt(2)(sqrt(δ)+2sqrt(nr)).       (7.2)

The Gaussian quadratic characteristic-function formula gives, for ell≥1,

    |E exp(i ell t q_F)|
                   ≤(1+4ell²t²(1−nr))^(-1/4).            (7.3)

Use (6.6), (7.2), (3.3) and tracial Duhamel for invariance. Use (6.4) at s=ell t and (7.3) for moments. The parameters (3.1) give a Gaussian invariance error

    16sqrt(2) ε(2^-10+2·2^-12)<ε/8

and a Gaussian moment bound<ε/4 because 4·16²(1−2^-24)>256.

Here are explicit checks of the finite-N budget:

    1+mt≤17m ε^-2,
    1+n r^-1/2≤2^13 n^(3/2) ε^-3,
    10^9·17³·2^39<2^84,
    500·16·2^36<2^50,
    sqrt(N)≥2^100 M^6m³n^(9/2)ε^-16.

The replacement term in (6.4) is≤2^-16 ε. The covariance term there and the finite-N invariance term are each≤2^-50 ε after dropping favorable powers of n,m,M and ε. All tests are therefore strictly below ε at every extreme trace.

Finally φ↦|φ(V^ell)| is continuous convex, while φ↦φ((α_h(V)−V)*(α_h(V)−V)) is continuous affine. Closed sublevel sets with the preceding strict margins contain every extreme trace and hence all T(C) by Krein–Milman. **This proves Theorem Q.** There is no covariance-subsequence argument in the row bound.

**Stress cases and limits.** Rank-one and full-rank covariance have the same lower variance control (7.1); zero eigenvalues are allowed. Large Følner sets are paid through n^9, not hidden in an ε-only constant. Infinite H requires new finite tests and a limit, not a direct conclusion of Q. Group dependence enters F; action dependence remains in the row realization and coordinate lifting. Fixing a nonscalar normalized element of Z supplies the same M across source applications, but no effective presentation of the rows is assumed. Fourier tests and L2 invariance are not operator-norm stability.

One must not apply positive functional calculus to the source's **symmetrized** empirical covariance. In M_4 with normalized trace take x_1=Z⊗I, x_2=Z⊗X, x_3=Z⊗Z, for Pauli involutions X,Z. They are centered variance-one contractions. The symmetrized 3×3 block matrix has diagonal I and blocks (12)=I⊗X, (13)=I⊗Z, (23)=0. Its quadratic form on (-2a,(I⊗X)a,(I⊗Z)a), for any unit vector a, is −2. It is not positive. The unsymmetrized matrix is Xrow*Xrow and is positive. This genuine matrix example tests a prescription; it is not a counterexample to any target.

## 8. C82: actual cost actions, with ergodicity paid

Use exactly

    A=F(a,b_1,…,b_99), w=ab_1ab_2…ab_99 a,
    J=<b_1,…,b_99,w>, Γ=A *_J (J×<t>),
    χ(a)=1, χ(b_i)=χ(t)=0.

The source proves the displayed J-generators freely generate J, and the amalgam embeds its factors; hence t has infinite order. Let X be the invariant conull free part of the right Bernoulli action on [0,1]^Γ, and

    Y_M=X×Z/MZ, (x,r)g=(xg,r+χ(g)), M>100.

Choose 0<α<1/200 with (e^96 96^99/95^95)α³<1/2 and η=α/100. The source gives Cost(X)≥1+η and Cost(Y_M)≤1+99/M. These are specified free pmp actions of the finitely generated Γ. **Neither inequality is asserted to be equality.**

The lower operations are already substantial. In group-actions.tex, actions:small-marker retains all t-edges and the 100 J-generators restricted to a Bernoulli marker of measure p; commutation with t gives the full J×<t> relation for cost 1+100p. Proposition actions:low supplies a-edges at 99 consecutive height fibers and uses w to obtain the next height repeatedly. The lower bound uses deployment:main's relative compression, models:transfer's passage from Bernoulli graphings to ranks of finite A-permutation presentations, and rank:main's sparse-overlap rank surgery. Those finite models are for the free subgroup A; they do not certify soficity of Γ or a rank lower bound for arbitrary replacement Γ-actions.

**Technical partial: the displayed Y_M are ergodic.** Restriction of the Bernoulli action to <t> is mixing. Cylinder functions depend on finite coordinate sets; their t^k-translates are disjoint for all sufficiently large |k|, since t has infinite order. Their correlations factor. Cylinder approximation gives mixing in L2 and thus ergodicity of this restriction. An invariant measurable subset of Y_M has at each height a t-invariant section in X, of measure zero or one. The a-action cycles the M heights, so all section measures agree. The whole subset has measure zero or one. The same restriction proves X ergodic. Freeness comes from its Bernoulli coordinate. Thus the source's actual examples already give **ergodic** actions of distinct costs for M>99/η. This short verification is technical, not C82.

**Failed bridge 1: invariant mixtures.** A disjoint union with weights s,1−s of two free actions is free and pmp. For 0<s<1 its components are invariant sets of intermediate measure, so it is not ergodic. Its cost is the weighted sum of the actual component costs: restrict a graphing to invariant components for the lower inequality and combine near-optimal component graphings for the upper inequality. This interpolates actual costs on a nonergodic action, not endpoint bounds on an ergodic action.

**Failed bridge 2: add a factor and retain cost.** Factoring onto an action does not give a lower bound retaining its whole cost. The source's own equivariant projection Y_M→X witnesses the failure: for large M the extension has strictly smaller cost. Hence a free/Bernoulli coordinate does not in general preserve cost. Adding group generators or free products changes the target unless separately justified. Abért–Weiss, retained v2, Theorem 1 and Corollary 2, concern weak containment and maximal Bernoulli cost; they give no ergodic intermediate-value principle.

The remaining obligation is an ergodic action of this **same** Γ with matching upper/lower cost equal to a prescribed c, or a family with a proved continuity/range theorem. The rank-transfer lower bound is tied to the Bernoulli action. No tunable matching lower estimate on a replacement action was obtained. C82 is unproved and unrefuted.

## 9. A82: the actual abstract-isomorphism obligation

Use the source's K=ell²(F_infinity), L=K⊗K, regular representations λ,ρ, and Pytlik–Szwarc deformation π_t. Its D_t is generated by λ(g)⊗1, 1⊗λ(g), 1⊗π_t(g), and 1⊗E_xy; it is unital separable with scalar center. Set

    P_a=C*(λ(g)⊗π_a(g):g∈F_infinity), a=0,t,
    E_D(P)={(d_n)∈prod D:d_n converges in norm to some p∈P}.

The source proves d_KK(E_D(P_0),E_D(P_t))≤2c(t)→0 and equal von Neumann closures. Its intrinsic coordinate projections lead from a spatial conjugacy to simultaneous normalizer approximations, excluded by the represented D'-tensor test. We retain that exact scope.

**Technical criterion.** For separable unital D with Z(D)=C1 and unital P,Q⊂D, the following are equivalent:

(a) E_D(P) and E_D(Q) are abstractly *-isomorphic.

(b) There are a unital *-isomorphism θ:P→Q and α_n∈Aut(D) such that for every p∈P,

    ||α_n(p)−θ(p)||→0.                                  (9.1)

**Proof.** The center of each sequence algebra is the convergent scalar sequences. Its minimal nonzero central projections are the coordinate e_n; their generated closed ideal is c_0(N,D). An isomorphism permutes e_n, preserves this ideal, and induces θ on the quotient P→Q. Each coordinate-corner restriction is an automorphism α_n of D. The image of a constant sequence p converges to θ(p). Any permutation of N preserves convergence, so (9.1) follows.

Conversely define (d_n)↦(α_n(d_n)). If d_n→p, isometry of α_n and (9.1) imply convergence to θ(p), giving an isometric *-homomorphism into E_D(Q). For b_n→q and p=θ^(-1)(q),

    ||α_n^(-1)(b_n)−p||≤||b_n−q||+||q−α_n(p)||→0.

The homomorphism is onto and proves (a). This is the abstract version of a source coordinate-corner operation, not a substantial new invariant. ∎

For A82 the criterion asks about this **actual** Aut(D_t)-orbit closure. Spatial normalizers give α_n=Ad(U_n) and are excluded by the source. Arbitrary α_n need not be implemented in the given representation, or even extend normally to D_t''. The test uses the represented commutant D_t', so invariance under all abstract automorphisms remains unpaid.

One approach would identify a characteristic essential ideal in D_t, prove every automorphism preserves an appropriate semifinite trace and its normal representation class, and transfer the spatial obstruction. This needs actual ideal, trace-scaling and representation-multiplicity arguments. Scalar center, unitarizability and universal similarity do not provide them. Making a bounded homomorphism similar to a *-homomorphism does not identify arbitrary *-representations.

A second approach would formulate an intrinsic inclusion invariant without D', prove Aut(D)-invariance and closure under the simultaneous convergence (9.1), and distinguish the actual P_0 and P_t. The represented tensor test is not automatically intrinsic. No replacement with all three properties was established. We assert neither abstract nonisomorphism nor an abstract countermodel as a target counterexample.

## 10. Contribution comparison, evidence, and handoff

The new-to-project contract is (3.1)–(3.2): one positive-covariance prescription with a polynomial row budget for all trace tests and translated forms. What was already paid is substantial: commuting orbit rows, extreme-trace independence, rank-uniform Gaussian normalization, same-realization translation control, trace weighting and absorption are in the equivariant source; row regularization is in its Cuntz companion; differentiable Taylor/Lindeberg replacement is explicitly discussed in Banna–Cébron. This report supplies the finite estimates and checks their hypotheses rather than importing a free-probability theorem. It does not produce a new action class, coordinate-lifting algorithm or invariant range. Under the project's strict standard, the author does **not** propose counting Q82 among the remaining two findings.

The complete search domain is inherited by immutable reference from I79: 13,223 tree entries, 749 manuscripts, 10,373 original blobs, consisting of 9,340 cached text bodies and 1,033 additional bodies (776 PDFs with retained extraction and 257 other files). The 619 MB evidence was neither redownloaded nor copied. Three retained searches inspect the exact 10,373-member text/byte-view domain: PDFs via their retained extraction, other bodies decoded with UTF-8 replacement. Path/line/text multisets preserve multiplicity. Metadata/search coverage is not a claim to have read every paper. All named relevant operator companions are in the selected manifest; the complete-domain lexical search is a bounded screen, not worldwide novelty certification. Expressions, counts and immutable domain identities are in searches.json and immutable-references.json.

Five external primary PDFs (including two Banna–Cébron versions), their retained text, four version pages, request timestamps, response statuses/headers, hashes and search responses are in the owned source directory. Current arXiv pages record observed version histories; BOT v1 and Abért–Weiss v2 are explicitly historical body choices. The Banna–Cébron author-hosted PDF prints November 13, 2018; the separately retained arXiv v3 prints February 16, 2022. Both retain the relevant replacement theorem and differentiable-function remark; the newer statement was checked directly. No unavailable full text is treated as read. Primary comparisons are bounded to the retained passages, not a claim that each paper was exhaustively audited.

Pre-seal history retains the failed polynomial-budget route, unsupported independent-block covariance identification, indefinite symmetrized covariance, and widening of a tentative safety constant from 2^180 to 2^200 before sealing. The report-writing tool syntax failure occurred before any report bytes were written and is recorded; the smaller successful writes followed. No previous report or seal was repaired. The finite exact diagnostics test the matrix Gram factorization, negative symmetrized quadratic form, nonidentical tensor-row moments, rank-varying/singular variance, height propagation, Bernstein envelopes and symbolic parameter budget. They do not prove the functional calculus, trace argument or significance.

Run from openai-proof-research:

    PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i82_measured_group_operator_discovery/verify.py

Primary links: [Szabó–Wouters published paper](https://msp.org/apde/2025/18-6/apde-v18-n6-p02-p.pdf), [Banna–Cébron v3](https://arxiv.org/abs/1811.05373v3), [Abért–Weiss v2](https://arxiv.org/abs/1103.1063v2), and [Burger–Ozawa–Thom v1](https://arxiv.org/abs/1010.0565v1). These support the scoped comparisons above.

The offline READ-ONLY verifier checks the exact owned domain, immutable report/artifact seal, frozen inputs, immutable references, all original corpus/outside blobs against the complete Git tree and retained hashes, five primary and eleven selected upstream PDF extraction replays (all 776 inherited extraction hashes are checked), bound passages, exact search multisets and unchanged diagnostic output. The four named live ledgers alone may drift; their snapshots stay immutable and live differences are informational. Verification never fetches, rewrites sources, repairs or reseals. The seal and its SHA-256 anchor cover this report and the two owned directories, with explicit self/anchor exclusion. No parent wrapper is included.

The retained pre-seal read-only run passed: 9,340 corpus Git blobs, 1,033 outside Git blobs, all 776 inherited PDF extraction hashes, five primary and eleven selected upstream PDF replays, 67 bound passages, and search multisets of 278, 833 and 65 lines. The exact diagnostic output passed unchanged. All four live ledger differences were informational; their frozen snapshots matched. A final default-mode run checks the completed seal as well.

**Separate verdicts:** evidence PASS means checks reproduce; Theorem Q is an author-level complete proof; contribution is assessed here as technical; C82 and A82 retain the stated gaps. Independent review would still need to check rectangular Lp normalization, row-level Taylor cancellation, regularization and the full constant budget. Integrity and finite matrices are not an independent proof verdict.
