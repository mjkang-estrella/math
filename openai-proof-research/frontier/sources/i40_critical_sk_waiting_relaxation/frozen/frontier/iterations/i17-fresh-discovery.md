# I17 fresh discovery: an exact six-point spherical Ramsey certificate

Research date: 2026-10-09. Assumed corpus: **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** throughout. Status: **complete candidate for separate fresh proof and significance reviews; not accepted or counted**. Four findings remain accepted (R006, R008, R009, R010). Worldwide priority is unverified.

**Proposed result.** Every nonempty spherical Euclidean set with at most six points is Ramsey. Consequently, for sets of at most six points, Ramsey is equivalent to spherical. Seven is the smallest cardinality of a spherical non-Ramsey set. The new part is a universal exact tensor certificate for six circle points, valid with arbitrary algebraic dependencies among their coordinates. The passage to other affine dimensions is a short quadratic-evaluation argument. The seven-point negative boundary is already in Pálvölgyi's primary manuscript; Section 6 also derives that known boundary directly from the pinned criterion.

The substantive bridge is **Möbius interpolation plus an invertible residual Jacobian that gives exact ideal membership in an algebraic local ring**. It is not a finite-jet sufficiency claim. The proof constructs a rational certificate, clears its denominators before mapping into the coordinate-field tensor ring, and therefore works even when that tensor ring has zero divisors. No formal series convergence, numerical approximation to real parameters, algebraic independence of the six parameters, or new Ramsey forcing theorem is assumed.

## 1. Frozen task and search scope

[full-brief.txt](../sources/i17_fresh_discovery/full-brief.txt) freezes the supplied brief, including the explicit resumption revoking historical pause instructions, the four-field screening requirement, excluded reductions, and the prohibition on agents, shared-index changes and commits. Byte snapshots of the rules, complete source inventory, full catalogue, ledger, frontier index, I13, I16 and task record are identified in [input-snapshots.json](../sources/i17_fresh_discovery/input-snapshots.json). Only this report and the assigned `frontier/{sources,experiments}/i17_fresh_discovery/` directories were written.

The complete `sources/preprints-tree.json` was parsed and every entry traversed: **13,223 entries, 10,373 blobs, 2,850 trees, `truncated:false`**. [complete-inventory-screen.json](../sources/i17_fresh_discovery/complete-inventory-screen.json) retains all paths and blob identities, plus every manuscript directory. This is complete inventory coverage, not a claim to have read every manuscript. Broad companion searches included circle, spherical, Euclidean, Ramsey, transitive, tensor, Saxl, subset-sum, SK and fluctuation titles. The Euclidean classification is the only directly relevant finite-configuration classification manuscript found in that complete inventory; graph Ramsey and circle-packing manuscripts concern different problems.

Eighty-five pinned TeX/BibTeX/README files from seven manuscripts were retrieved and verified against their Git blob identities. [pinned-manifest.json](../sources/i17_fresh_discovery/pinned-manifest.json) records immutable raw URLs, paths, blob SHA-1, SHA-256, byte lengths and retrieval times. [theorem-contracts.json](../sources/i17_fresh_discovery/theorem-contracts.json) retains exact labelled statement blocks and line ranges; [read-ranges.json](../sources/i17_fresh_discovery/read-ranges.json) identifies the selected statement/proof passages. Every mathematical corpus reliance below uses these actual files, not the catalogue or latest branch.

Primary literature was searched before formulation and again against the exact proposed scope. Version-bearing abstract pages and full HTML manuscripts are preserved with hashes in [literature/manifest.json](../sources/i17_fresh_discovery/literature/manifest.json). [primary-statement-contracts.json](../sources/i17_fresh_discovery/primary-statement-contracts.json) preserves 16 exact primary-literature statements with source offsets and hashes. A final [latest-branch comparison](../sources/i17_fresh_discovery/literature/latest-upstream-comparison.json) found the current GitHub commit identical to the assumed revision and all nine classification TeX files unchanged; this check is prior-art evidence only. The full current Pálvölgyi manuscript includes stronger appendix barriers; they were checked rather than inferred from its seven-point abstract. Its author labels the appendix claims unchecked. They are comparisons, not premises for our positive theorem.

## 2. Four distinct targets and the selection decision

### A. Exact six-point spherical Ramsey classification — selected

Pinned *A classification of finite Euclidean Ramsey configurations*, `01-introduction.tex`, `thm:classification`, says: for a finite set of at least two points `a_i` affinely spanning `R^d`, put `p_i=(1,a_i)`, let `F` be the field generated over Q by the coordinates, and put `B=F⊗_Q F`. Then the set is Ramsey exactly when some `(d+1)×(d+1)` matrix P over B satisfies

\[
 (p_i\otimes1)^T P(1\otimes p_i)=0\quad\text{for every }i,
 \qquad m(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d),
\]

where `m(x⊗y)=xy`. No symmetry or independent constraint on the constant row/column is required. Ramsey means that for every integer r≥2 there is D≥1 such that **every** r-coloring of R^D contains a congruent copy at the original scale. Colorings need not be measurable.

Actual proof interfaces read: `02-tensors.tex`, `alg:equivalence`, including tensor-flip symmetrization and coefficient descent; necessity; the final sufficiency proof in `06-groups.tex`; and the full relevant proofs in `07-consequences.tex`. `cons:quadratic` requires independent ordinary quadratic evaluation rows and uses an adjugate lift. `cons:quadrilateral` proves all sets of at most five circle points Ramsey. `cons:transitive` already covers all subtransitive sets. `cons:nine` is a generic nine-point tensor obstruction, and `cons:twelve` is a derivation example. None supplies the six-point certificate proved here. For six circle points the ordinary quadratic-evaluation rank is five, so the hypothesis of `cons:quadratic` fails precisely at the selected boundary.

Primary comparison: [Pálvölgyi, arXiv:2609.23327v1](https://arxiv.org/html/2609.23327v1), latest version shown on the retrieved abstract page, Theorem 1 gives an explicit non-Ramsey heptagon. Appendix A.2/A.11 excludes fixed weighted first-derivative energy obstructions for ≤6 spherical points, A.4 handles finite combinations of derivations, and A.15–A.17 discuss stronger restricted obstruction classes. These statements do **not** establish Ramseyness. Our positive certificate supplies the missing implication by a different mechanism. Section 7 gives the narrower significance assessment.

### B. Symmetric/exterior refinement of Saxl — unresolved, not counted

The target was the Bessenrodt–Bowman refinement: split staircase-square support between `Sym² S^{ρ_m}` and `Λ² S^{ρ_m}`, rather than merely their sum. The pinned universal-square theorem already covers every irreducible for each degree outside {2,4,9}, and its unipotent transfer is already a corollary. The stronger companion *A Cyclic Polytabloid Proof of Saxl's Conjecture*, `thm:cyclic-saxl`, supplies every irreducible in the **specified** cyclic module `W_m=C[S_N](v_R⊗v_C)`. We read its definition, band-quotient proof and completion of induction. `prop:band-quotient` gives the full induced quotient from `W_{m-s}⊠U_{m,s}`; it does not specify the flip eigenspaces of the resulting constituent multiplicity spaces.

The concrete attempted bridge was to replace the cyclic generator by `(v_R⊗v_C ± v_C⊗v_R)/2` and propagate the band quotient with its flip action. Ordinary support does not make both projections nonzero: the missing datum is the flip trace on each target multiplicity space (and compatible noncancelling band pairings). As a small exact check, for S3 the staircase representation (2,1) has square `1⊕sgn⊕standard`, while its symmetric square is `1⊕standard` and its exterior square is `sgn`. Thus a support-only induction cannot assign constituents to both signs. This is not a disproof of the refined conjecture.

[Bessenrodt–Bowman, *Splitting Kronecker squares…*, arXiv:2202.03066v3](https://arxiv.org/html/2202.03066v3), Section 10, Conjecture 10.2, already states the precise expected exceptional constituents: the symmetric part omits sign when m≡2 mod 4; the exterior part omits `(N)`, `(N−1,1)`, `(N−2,2)`, also sign when m≢2 mod 4, and additionally `(2,2,2)` for m=3. The candidate would need a new flip-sensitive quotient argument, not a claim that ordinary Saxl solves this. No such argument is completed here.

### C. Sub-half-exponential counting from random-phase subset-sum checksums — a precise estimator obstruction

Target: estimate the number Z of exact subset-sum solutions at the source's improved decision exponent, using repeated phase checksums rather than isolation. Pinned *Subset Sum in Time 2^{0.49n}*, `thm:main`, gives a uniform randomized decision algorithm on positive integer inputs, success ≥2/3 on each input, and the stated bound on every random execution when the input bit length is bounded by any fixed power of n. Its stronger `checksum.tex`, `thm:checksum`, estimates an arbitrary modular-bin phase sum to absolute error 1/8 with probability 1−o(1), retaining the independent uniform phases; we read the exact statement and its variance/resource proof. The decision proof isolates a solution and subtracts aliases. The low-space companion gives decision in polynomial-times `2^{n/2}` time and polynomial-times `2^{0.199n}` writable words. Neither theorem counts all exact solutions.

Even granting an **exact** true-bin phase sum `S=Σ_{I solution}∏_{i∈I}z_i`, the unbiased estimator `|S|²` need not have polynomial relative variance. Take k blocks with two equal positive weights `3^j` in block j, j=0,…,k−1, and target `Σ3^j`. Unique ternary expansion forces exactly one choice per block. Thus `Z=2^k`, and `S=∏_j(z_{j,0}+z_{j,1})`. For independent uniform Pth roots with any integer P≥3,

\[
 E|z_0+z_1|^2=2,\qquad E|z_0+z_1|^4=6,
 \qquad\frac{\operatorname{Var}|S|^2}{(E|S|^2)^2}=(3/2)^k-1.
\]

The two moment identities follow by expanding and using root orthogonality (the differences in exponents are at most two). Independence multiplies them. With s independent trials, the relative mean-square error is exactly `((3/2)^k−1)/s`. This blocks this phase-energy estimator even with perfect checksum computation; it is not a lower bound for all counting algorithms. These particular inputs are easy by distinct-sum compression, so the example does **not** rule out a hybrid using that branch. A new variance bound restricted to the complementary high-support regime, or a different counting estimator, remains necessary. This is a fresh mechanism screen, not I13's inverse-fiber estimator repeated under a new name.

Primary boundary check: [Randolph–Węgrzycki, *Beating Meet-in-the-Middle for Subset Balancing Problems*, arXiv:2511.10823](https://arxiv.org/abs/2511.10823) concerns finding a nonzero coefficient vector for specified coefficient sets. Its actual theorem statements do not supply exact multiplicity counting for ordinary subset sum. No worldwide algorithmic priority claim is made.

### D. A joint low-temperature SK fluctuation law at distinct temperatures — unproved coupling estimate

Target: for fixed distinct β1,β2>1 and the **same** Gaussian disorder, prove full-sequence convergence of `(n^{-1/6}(F_n(β_j)−EF_n(β_j)))_{j=1,2}`, with a characterized nontrivial covariance. This is distinct from qualitative mixing-to-CLT and from the source's already established single-temperature law.

Pinned *The low-temperature Sherrington–Kirkpatrick free-energy limiting law*, `thm:main` and `thm:moments`, already gives each scalar limit, positive variance prefactor, all fixed-moment convergence at power rates and uniform local exponential moments. Its `red:prop-moments` proof obtains scalar moments from stopped size-comparison bounds. Its corollaries already include fixed subcritical Curie–Weiss coupling and sufficient disorder-chaos scales; these are excluded duplicates. The fluctuation-scale companion's **Common prelimit temperature** passage, read with its proof, permits a common `T_n→T_∞>1`, held fixed throughout each parent–child construction. It does not give separate physical temperatures on different retained labels.

The unresolved step is a summable size comparison for a genuinely joint transform such as `log E exp(q1Y_n(β1)+q2Y_n(β2))`. Its coupled replicas have cross covariance proportional to β1β2 and two different scalar Parisi reference paths. The single common-temperature calibration does not identify the mixed overlap centers or provide the needed inverse estimate. Marginal power rates and exponential moments give tightness and subsequential mixed moments, but do not force uniqueness of the joint subsequential law. No joint law is asserted. Primary comparisons were screened for their regimes: the current critical-window paper arXiv:2609.07446 has β_n→1, and Chen–Dey–Panchenko arXiv:1509.07071 treats nonzero external field. Neither is silently substituted for this fixed, zero-field, two-temperature contract.

**Selection.** A has an exact finite-dimensional algebraic construction with a verifiable nonsingular matrix. B and D need new representation/coupled-overlap estimates; C has a proved obstruction to the proposed estimator but an untested high-support repair. Develop A, and do not count the other screens.

## 3. Universal local interpolation lemma

All rings and polynomials in this section are explicitly specified. Fix a field F of characteristic zero and six **distinct** elements `t_1,…,t_6∈F`. Introduce independent formal variables `U_1,…,U_6`, and let

\[
 \mathfrak m=(U_1-t_1,\ldots,U_6-t_6),\qquad
 R=F[U_1,\ldots,U_6]_{\mathfrak m}.
\]

Evaluation `ev:R→F` at U=t is well defined: every inverted denominator has nonzero value there. The symbols x,y below are separate polynomial variables, not the U parameters.

**Lemma 1 (exact six-pair lift).** There is a polynomial `Q(x,y)∈R[x,y]` of degree at most two in each variable such that

\[
 Q(t_i,U_i)=0\quad(1\le i\le6),\qquad
 \operatorname{ev} Q(x,y)=(y-x)^2.
 \tag{1}
\]

Here `ev` acts on coefficients only. It does not set the independent variables x,y equal.

### 3.1 Basis and elimination of five evaluation equations

Use the following basis of the nine-dimensional space of bidegree ≤(2,2) polynomials:

\[
\begin{aligned}
 h_0&=1,& h_1&=(x+y)/2,&h_2&=xy,\\
 h_3&=xy(x+y)/2,&h_4&=x^2y^2,\\
 a_0&=y-x,&a_1&=y^2-x^2,&a_2&=xy(y-x),\\
 J&=(y-x)^2.
\end{aligned}\tag{2}
\]

The h's specialize on y=x to `1,x,…,x^4`; the a's are the three skew-symmetric basis polynomials, and J completes the symmetric part. This also proves independence of the displayed basis.

Put `H_{iℓ}=h_ℓ(t_i,U_i)` for i=1,…,6 and ℓ=0,…,4. Write H0 for its first five rows, and H6 for its last row. At U=t, H0 is the Vandermonde matrix `(t_i^ℓ)_{i≤5,ℓ≤4}`, so its determinant is nonzero. It is invertible over R. For a fixed bivariate polynomial f of bidegree ≤(2,2), define the residual

\[
 r_f=f(t_6,U_6)-H_6H_0^{-1}
       (f(t_1,U_1),\ldots,f(t_5,U_5))^T.
 \tag{3}
\]

It is R-linear in f. Its vanishing means that f's six values can all be removed using the five h columns. In particular `r_{h_ℓ}=0` identically.

### 3.2 An exact three-parameter comparison family

Solve for a,b,c over R from

\[
 a t_i+b-c t_iU_i=U_i\qquad(i=1,2,3).
 \tag{4}
\]

The coefficient rows are `(t_i,1,−t_iU_i)`. At U=t their determinant is a nonzero Vandermonde multiple, and the solution is `(a,b,c)=(1,0,0)`. Thus a,b,c are rational functions of `U_1,U_2,U_3`, regular at their base point. Every `ct_i+1` and `a−bc` is a unit in R. Set

\[
 \phi(z)=\frac{az+b}{cz+1},\qquad
 v_i=U_i-\phi(t_i)\quad(i=4,5,6).
 \tag{5}
\]

For i≤3, (4) gives `U_i=φ(t_i)` exactly. Substitution of `φ(t_i)` for U_i, i=4,5,6, defines an endomorphism σ of R fixing U1,U2,U3 and the coefficient field F. It preserves the base point, so sends inverted polynomials to units.

For every f under consideration,

\[
 \sigma(r_f)=0.\tag{6}
\]

To prove this, on the substituted family every pair is `(t_i,φ(t_i))`. Multiplication of `f(z,φ(z))` by `(cz+1)^2` gives a polynomial in z of degree at most four: for a monomial `x^p y^q` it is `z^p(az+b)^q(cz+1)^{2-q}`, of degree at most p+2≤4. Consequently every such six-value vector lies in the rank-five module

\[
 \left\{\left(\frac{g(t_i)}{(ct_i+1)^2}\right)_{i=1}^6:
                         \deg g\le4\right\}.
\]

Its first five coordinates determine it, by the Vandermonde inverse and the unit denominators. The substituted h columns form a basis: their first-five matrix remains a unit matrix determinant at the base point. They therefore interpolate the sixth value as well, proving (6) over the localized coefficient ring, not merely at individual numerical Möbius maps.

For explicit coefficients, define σ_k, k=0,1,2,3, by leaving the first k tail variables from the ordered list (U4,U5,U6) unchanged and substituting φ in the other tail variables. Thus σ_0=σ and σ_3=id. For any r with σ(r)=0, set

\[
 C_k(r)=\frac{\sigma_k(r)-\sigma_{k-1}(r)}{v_{k+3}}
 \quad(k=1,2,3).
 \tag{7}
\]

This quotient is an element of R, even when v is zero at the base point. Indeed for a polynomial the numerator is divisible by `U_{k+3}−φ(t_{k+3})`. For a rational function write the difference over the product of its two substituted unit denominators; its numerator is again divisible. This proves both regularity and the exact telescoping identity

\[
 r=\sum_{k=1}^3C_k(r)v_{k+3}.\tag{8}
\]

In particular define

\[
 A_{jk}=C_k(r_{a_j})\quad(j=0,1,2;\ k=1,2,3),
 \qquad b_k=C_k(r_J).
 \tag{9}
\]

With column v=(v4,v5,v6), these give `r_a=Av` and `r_J=bv` **exactly**. This is the ideal-membership step; no implicit-function theorem or formal lifting assertion replaces it.

### 3.3 The residual Jacobian is invertible and the correction vanishes at the diagonal

Let

\[
 H_*(z)=\prod_{i=1}^6(z-t_i),\qquad
 \mu_i=\frac{H_*'(t_6)}{H_*'(t_i)}.
 \tag{10}
\]

Then μ6=1, all μi are nonzero, and

\[
 \sum_{i=1}^6\mu_it_i^j=0\quad(0\le j\le4).\tag{11}
\]

For completeness, Lagrange interpolation of a degree≤4 polynomial at six nodes has coefficient of z5 equal to zero; that coefficient is `Σ f(t_i)/H_*'(t_i)`. Multiplication by `H_*'(t_6)` gives (11). Hence `(μ_i)` is the residual row `(-H_6H_0^{-1},1)` evaluated at U=t.

Each a_j and J vanishes on y=x. Differentiating (3) at the base point consequently differentiates only f's values: the derivative of the residual row multiplies a zero vector. Thus

\[
 \left.\frac{\partial r_f}{\partial U_k}\right|_{U=t}
      =\mu_k(\partial_yf)(t_k,t_k).
 \tag{12}
\]

In (7), φ depends only on U1,U2,U3, so evaluation of its tail divided difference is precisely this tail partial derivative. Therefore

\[
 \operatorname{ev}A=
 \begin{pmatrix}
 \mu_4&\mu_5&\mu_6\\
 2\mu_4t_4&2\mu_5t_5&2\mu_6t_6\\
 \mu_4t_4^2&\mu_5t_5^2&\mu_6t_6^2
 \end{pmatrix},\qquad \operatorname{ev}b=0.
 \tag{13}
\]

In particular

\[
 \det(\operatorname{ev}A)
 =2\mu_4\mu_5\mu_6(t_5-t_4)(t_6-t_4)(t_6-t_5)\ne0.\tag{14}
\]

A is therefore invertible in R. Put `c=bA^{-1}`, a row with three components. Equations (8)–(9) give

\[
 r_J=c\,r_a,\qquad \operatorname{ev}c=0.\tag{15}
\]

Set `f=J−Σ_{j=0}^2c_j a_j`, and let

\[
 d=H_0^{-1}(f(t_1,U_1),\ldots,f(t_5,U_5))^T,
 \qquad Q=f-\sum_{\ell=0}^4d_\ell h_\ell.
 \tag{16}
\]

The first five evaluations of Q vanish by construction; the sixth vanishes by (15) and the definition of the residual. At U=t, c=0, all f(t_i,t_i)=0, and consequently d=0. Thus `ev Q=J`. This proves Lemma 1. ∎

## 4. Clearing denominators and producing the tensor certificate

**Lemma 2 (descent without a domain assumption on the tensor ring).** Let F be a subfield of the real numbers generated over Q by six distinct real numbers t_i. Put B=F⊗_Q F and q(t)=(1,t,t²)^T. There is a matrix K over B such that

\[
 (q(t_i)\otimes1)^T K(1\otimes q(t_i))=0\quad(1\le i\le6),
 \qquad
 m(K)=J_0:=\begin{pmatrix}0&0&1\\0&-2&0\\1&0&0\end{pmatrix}.
 \tag{17}
\]

**Proof.** Apply Lemma 1 over this actual F; the six formal U variables remain independent, regardless of any relations among the actual t_i. Choose a common polynomial denominator Δ(U)∈F[U] for the nine coefficients of Q, with Δ(t)≠0. This is possible because all coefficients lie in the explicitly defined local ring. Then E(x,y)=Δ(U)Q(x,y) has coefficients in F[U]. Its evaluation identities `E(t_i,U_i)=0` are polynomial identities in F[U]: they hold in its localization, and F[U] is a domain. No property of B is used here.

Define the polynomial-ring homomorphism

\[
 \iota:F[U_1,\ldots,U_6]\longrightarrow B,
 \quad a\longmapsto a\otimes1,\quad U_i\longmapsto1\otimes t_i.
\]

Write `E(x,y)=Σ E_{αβ}(U)x^αy^β`, α,β=0,1,2, and put

\[
 K_{\alpha\beta}=(\Delta(t)^{-1}\otimes1)\,\iota(E_{\alpha\beta}).\tag{18}
\]

The polynomial identities give the tensor equations. Since `m∘ι` is evaluation at U=t, multiplication gives `m(K)=J0`. We never invert ι(Δ) in B, and never specialize the entire coordinate field to a rational numerical tuple. Hence algebraic dependencies and zero divisors in B cause no problem. ∎

**Theorem 3 (six circle points).** Every set of six distinct points on a Euclidean circle is Ramsey, under the pinned classification theorem.

**Proof.** Ramsey status is invariant under Euclidean similarities: translation and orthogonal maps preserve copies, and for a fixed scale r>0, pulling a coloring back by `x↦rx` transfers the forcing property in either direction. Normalize the circle to the unit circle in R². Rotate it so none of the finitely many points is (−1,0). Write

\[
 a_i=\left(\frac{1-t_i^2}{1+t_i^2},\frac{2t_i}{1+t_i^2}\right),
 \qquad t_i=\frac{(a_i)_2}{1+(a_i)_1}.
\]

The parameters are distinct, and the coordinate field is exactly F=Q(t1,…,t6). No three circle points are collinear, so the set affinely spans R². Put p(t)=(1,a(t))^T and

\[
 L=\begin{pmatrix}1&0&1\\1&0&-1\\0&2&0\end{pmatrix},\qquad
 S=\operatorname{diag}(-1,1,1).
\]

Then `p(t)=Lq(t)/(1+t²)` and `L^T S L=−2J0`. Use K from Lemma 2 and set

\[
 P=-2L^{-T}KL^{-1}.\tag{19}
\]

Its tensor evaluations on p_i vanish, as the denominators `1+t_i²` are nonzero and the corresponding separate tensor factors are units. Its multiplied matrix is exactly S, whose spatial block is I2. The precise hypotheses of `thm:classification` are satisfied, so the configuration is Ramsey. Undo the similarity. ∎

## 5. All spherical sets of at most six points

**Lemma 4 (the only small quadratic dependence).** Let A be a spherical set of at most six distinct points. If its ordinary quadratic evaluation rows are dependent, then A consists of six points on a circle.

**Proof.** Take a nonzero relation among the rows and restrict to the support of its coefficients λ_i≠0. Say the support has m points and affine dimension d. On F^m, or simply on R^m, the diagonal bilinear form `B(u,v)=Σ λ_i u_i v_i` is nondegenerate. Let W be the evaluation vectors of affine functions on this support. Its dimension is d+1. The quadratic relation says B vanishes on W×W, hence `W⊂W^⊥` and `2d+2≤m≤6`.

If d≤1, sphericity gives at most two points on that affine subspace (one for d=0). These possibilities contradict `2d+2≤m`. Thus d=2, m=6. The support is all of A, and its affine plane intersects the sphere in a circle of positive radius. ∎

The isotropic-space observation is classical and also appears in Pálvölgyi's appendix; it is not the new mechanism being counted.

**Theorem 5 (small-cardinality characterization).** Under the stipulated corpus, for every nonempty finite set A in any finite-dimensional real Euclidean space with |A|≤6,

\[
 A\text{ is Ramsey}\quad\Longleftrightarrow\quad A\text{ is spherical}.
\]

In particular, for every such spherical A and every integer r≥2, there exists a finite D such that every function `R^D→{1,…,r}` is constant on a congruent copy of A, with all original distances preserved.

**Proof.** Necessity is the pinned `cons:spherical` (including the immediate singleton case). For sufficiency, pass to the affine span. Sphericity persists there by orthogonally projecting the center and subtracting its squared normal distance from the squared radius; for ≥2 distinct points the resulting radius is positive. A singleton is immediate. If quadratic rows are independent, apply the pinned `cons:quadratic` with its actual hypotheses. Otherwise Lemma 4 puts us in Theorem 3. ∎

This is one finding, including its planar case, higher-dimensional small-set consequence and sharp cardinality interpretation. No numerical dimension bound D(A,r), subtransitive embedding, canonical Ramsey property or statement about larger spherical sets is asserted.

## 6. Sharpness: a direct check of the already-known seven-point boundary

Pálvölgyi's Theorem 1 supplies a seven-point circle counterexample. To make the sharpness implication depend only on the stipulated classification, the following short alternative proves the already-known generic-seven conclusion. It is a boundary check, not a second new result.

Choose seven algebraically independent real parameters t1,…,t7, and take their unit-circle images a_i. Suppose a tensor certificate P existed. Average P with its tensor flip-transpose as in pinned `alg:equivalence`. Its multiplied matrix H is then symmetric, with spatial block I2. The multiplied evaluations give `H00+2H01 x_i+2H02 y_i+1=0`. Three noncollinear points force `H00=−1`, `H01=H02=0`, so H=S. After conjugation put `K=−L^TPL/2`; its multiplied matrix is J0.

Let F=Q(t1,…,t7), choose the monic cubic `g(z)=z³`, and define a homomorphism from B to F[[ε]] by left scalars fixed and right scalars

\[
 1\otimes f(t_1,\ldots,t_7)\longmapsto
 f(t_1+\varepsilon g(t_1),\ldots,t_7+\varepsilon g(t_7)).
\]

This is well defined: algebraic independence presents F as a rational function field, and every nonzero denominator has its original nonzero value as constant term. The image of K yields a bivariate polynomial series `Q_ε=J+εQ1+ε²Q2+…`, each coefficient of bidegree≤(2,2), with

`Q_ε(t_i,t_i+εg(t_i))=0` for all seven indices.

At first order `Q1(t_i,t_i)=0`, since `∂_yJ(t,t)=0`. The degree≤4 polynomial `Q1(z,z)` has seven distinct roots, so is identically zero. Therefore Q1 belongs to the span of `J,a0,a1,a2`, and `(∂_yQ1)(z,z)` has degree at most two. The ε² equation is

\[
 g(t_i)^2+g(t_i)(\partial_yQ_1)(t_i,t_i)+Q_2(t_i,t_i)=0.
\]

Let `H7(z)=∏_{i=1}^7(z−t_i)` and λ_i=1/H7'(t_i). Lagrange interpolation gives `Σλ_i t_i^j=0` for j≤5 and `Σλ_i t_i^6=1`. The weighted sum of the last equation is consequently `1+0+0=0`, a contradiction. Thus this seven-point spherical set is not Ramsey. Together with Theorem 5, the minimum cardinality is exactly seven. ∎

Finite jets are used here only as a **necessary** obstruction to an assumed exact certificate. The positive six-point argument instead constructs exact rational functions and clears denominators. This is the distinction missing from the preliminary I16 screen.

## 7. Prior art, significance and review limits

The named problem is the Erdős–Graham–Montgomery–Rothschild–Spencer–Straus/Graham spherical Ramsey characterization, more precisely its **sharp small-cardinality boundary after accepting the general tensor classification and the known spherical counterexamples**. The corpus has already disproved the general spherical conjecture and the necessity of subtransitivity. This candidate does not claim to solve those again. It resolves the remaining six-point positive boundary and identifies the smallest possible spherical counterexample.

The strongest direct comparisons are:

1. Pinned family 172: all ≤5 circle points by **full row rank**, plus subtransitive sets. Six rows have rank five; the adjugate proof there cannot be applied without a new lifting step. Our proof handles the exact rank drop by a Möbius comparison family, three residual ideal generators and their nonsingular diagonal Jacobian.
2. Pálvölgyi v1, main theorem and stronger appendix: a seven-point counterexample and barriers to particular negative invariants below seven. We read the explicit main proof, A.2, A.4, A.8–A.11 and the later finite-jet barriers. They do not construct a positive tensor certificate. We do not infer a general positive theorem from failure of those obstructions.
3. Classical Lagrange interpolation, fractional-linear three-point interpolation, local denominator clearing and the isotropic dimension bound are standard ingredients. The proposed contribution is their exact combination proving (6)–(16) and then descending it through (18), not a claim to have invented those ingredients.

The current primary-source searches did not locate this six-point theorem or this certificate. That is a bounded search result, not proof of worldwide priority. A secondary search hit described six circle points as still open; it was not used as mathematical evidence. The nearest retrieved MathDB item, [the one-point extension conjecture](https://mathdb.com/p/375277/the-one-point-extension-conjecture-for-euclidean-ramsey-sets), explicitly requires the added point outside the old hyperplane. It is a different statement and does not subsume a sixth point in the same circle. No exact six-point MathDB item, verified ranking or featured designation was established. Accordingly **no MathDB significance score or ranking is asserted**; the fresh significance reviewer should assess the exact threshold result itself and report any ranking requirement still unmet. This is a material limit of the present handoff, not a reason to invent a score or relabel the theorem as solving that different MathDB problem.

The mathematical dependency is the pinned classification, with its quadratic-interpolation consequence. Its Ramsey forcing proof is assumed true as instructed; this report independently proves the new algebraic lift and geometric deductions. No public submission, human peer review, independent AI proof pass or formal proof certification is claimed. Separate fresh proof and significance reviews remain required before acceptance.

Priority audit targets: exact six-point circle/spherical statements; any local interpolation theorem that already gives the lift; current revisions of the classification and heptagon manuscripts; and whether the substantial bridge meets the project's contribution standard after all pinned inputs are granted. The known generic-seven calculation and Lemma 4 should receive no independent count.

## 8. Diagnostics, source contracts and sealed handoff

Run from this workspace:

```sh
python frontier/experiments/i17_fresh_discovery/diagnostics.py
python frontier/experiments/i17_fresh_discovery/series_diagnostics.py
python frontier/experiments/i17_fresh_discovery/verify.py
```

The deterministic standard-library diagnostic verifies **140 exact rational evaluations** of the entire certificate construction: fractional-linear interpolation, vanishing on its comparison family, telescoping residual factorization, the invertible three-by-three solve, and all six final bivariate evaluation equations. It independently checks 140 diagonal Jacobian determinant formulas and the circle-coordinate congruence `L^TSL=−2J0`. All arithmetic is rational. The seven-point check verifies the Lagrange-weight cubic-square obstruction. The subset-sum check enumerates the solution counts and fourth moments for one through five blocks. An additional exact truncated-power-series diagnostic checks **72 equations through order seven in 12 parameter directions**, including the certificate's diagonal value; it is explicitly supplementary to the exact proof.

Rational T/U evaluations are evaluations of the **formal interpolation formulas**, not numerical specialization of an entire transcendental coordinate field and not a proof of universal Ramsey status. The universal proof is Sections 3–5. Likewise the second-order seven-point diagnostic does not prove a finite-dimensional coloring statement by itself; the classification plus Section 6 does.

[artifact-manifest.json](../sources/i17_fresh_discovery/artifact-manifest.json) seals this report, sources, scripts, input snapshots, contracts and diagnostic outputs, excluding only itself and its derived verification output. [verification.json](../sources/i17_fresh_discovery/verification.json) records source-blob recomputation, exact statement/proof-range hashes, input snapshot identities and artifact checks. Live shared inputs are compared separately with the frozen bytes so concurrent parent edits cannot silently replace a premise.

**Handoff recommendation:** send the universal six-pair lift and its spherical consequence to a fresh proof reviewer, then obtain a separate current-primary-literature significance review. Focus proof review on the algebraic substitution in (6), regularity of (7), determinant (14), and the clear-before-map descent (18), including algebraically dependent parameter fields. Do not promote this report or any other screened route to the accepted ledger before those reviews and parent verification.
