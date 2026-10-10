# I17 six-point spherical Ramsey candidate — independent proof review R2

**Verdict: PASS, relative to the stipulated pinned classification. No mathematical repair or additional hypothesis is required.**

The candidate's exact local-ring construction, its clear-before-map descent, the geometric reduction, and its independent seven-point obstruction all hold. This is a proof verdict only. It does not assign a finding number, change the accepted count, establish novelty/significance, or authorize publication by this reviewer.

**Important for the separate significance audit:** the reviewer found a substantially shorter *polynomial* certificate: split the six pairs into two triples, construct a bilinear vanishing factor for each triple, and multiply them. An adjugate gives a universal formula with only nonzero scalar Vandermonde normalization. Section 5 proves this completely; the independent symbolic check verifies it with all twelve parameters formal. This is a simplification of a valid proof, not a repair. Any subsequent assessment of the claimed nonroutine mechanism should consider this factorization, not only the length of the residual-Jacobian construction.

Review date: 2026-10-09. Assumed revision: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## 1. Frozen object, scope, and conventions

The full candidate read and reviewed is `frontier/iterations/i17-fresh-discovery.md`, 367 lines, SHA-256 `87b86401ed5c1d554715c78fa203e33acb0117fd8255357e495a882842c0feb8`. The original research brief, full R2 brief, AGENTS.md, operative TEN-FINDINGS.md, I16 checkpoint, candidate source files, contracts, diagnostics, and author seal are frozen in [the R2 input manifest](../sources/i17_six_point_ramsey_r2/input-manifest.json). There are 155 snapshots. All were unchanged at final verification.

The reviewed conclusion is precisely: every nonempty spherical set of at most six **distinct** points in a finite-dimensional real Euclidean space is Ramsey. For every integer number of colors r≥2, there is some finite D≥1 such that every function from R^D to {1,…,r} has a monochromatic congruent copy at the original distances. D can depend on both the configuration and r. The converse is source spherical necessity. Seven is the smallest cardinality of a spherical non-Ramsey set, using the source-relative negative argument in Section 7 below. No measurable-coloring restriction, uniform/effective dimension, transitive embedding, or subtransitivity is being claimed.

Conventions needed for this exact statement:

- “Quadratic” means total degree **at most two**, including constant and affine terms. The source rows list all ordered products p_αp_β, with repeated off-diagonal columns. Removing those duplicate columns does not change row rank.
- All tensor products are over Q. The multiplication map m:F⊗Q F→F is applied entrywise to matrices. Row/column index zero is the constant coordinate.
- The symbols x,y in the bivariate construction are independent polynomial variables. Evaluating coefficients at U=t leaves x and y independent. It is not restriction to y=x.
- In the local proof, every t_i is a fixed element of the **actual** coefficient field F; the U_i remain independent indeterminates even when the t_i satisfy algebraic relations.
- A singleton is spherical under the source's convention and is Ramsey directly. Equivalently, it lies on a positive-radius sphere after an isometric embedding into a positive-dimensional Euclidean space; its projected affine-span radius can be zero. If one insists on a positive-radius sphere in the zero-dimensional space itself, that convention would exclude a singleton in R^0 and is not the source's convention. Every use of a positive radius in this proof concerns at least two distinct points.
- Passing to the affine span means choosing orthonormal affine coordinates, hence a congruent representative. Its coordinate field can change. The criterion is applied to that representative's own field; no preservation of an earlier coordinate field is assumed.

The other three screens in I17 are outside this positive proof review and are not findings. I16 was only a checkpoint: it supplied no positive theorem. Its objections to fraction-field rank, finite-jet sufficiency, and numerical specialization of whole coordinate fields remain correct; none is used as a positive inference here.

## 2. Actual pinned source contracts and dependency ledger

The actual manuscript read is *A classification of finite Euclidean Ramsey configurations*, directory `preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/`. All URLs below use the fixed revision. Full exact statements, source identities, and statement hashes are retained in [source-contracts.json](../sources/i17_six_point_ramsey_r2/source-contracts.json); actual statement/proof reading ranges and hashes are in [read-ranges.json](../sources/i17_six_point_ramsey_r2/read-ranges.json). The source's Ramsey forcing proof is stipulated true, not independently re-proved here.

1. **Classification and definition.** [01-introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/01-introduction.tex), read lines 1–193; Git blob `7124c465bde3ba0a9975aa4dcb6380c527173589`. `thm:classification`, lines 74–88, assumes s≥2 distinct points affinely spanning R^d, p_i=(1,a_i), their coordinate field F, and B=F⊗Q F. Its exact condition is the existence of P∈Mat_(d+1)(B) with
   
   `(p_i⊗1)^T P (1⊗p_i)=0` for all i and `m(P_αβ)=δ_αβ` for 1≤α,β≤d.
   
   There is **no** separate constraint on the multiplied constant row or column, no symmetry requirement on P, and no assumed domain property of B. Lines 3–8 specify arbitrary maps as colorings and exact original-scale congruence. Used for the six-point positive conclusion and seven-point negative conclusion.

2. **Tensor equivalence, symmetrization, and necessity.** [02-tensors.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/02-tensors.tex), read lines 1–229; Git blob `357a5dc4fab8c0f083541e90a009106372ac05da`. `alg:equivalence`, lines 33–36, and its proof identify tensor flip with `P*_{αβ}=τ(P_{βα})`; evaluation satisfies `E_i(P*)=τ(E_i(P))`. Thus `(P+P*)/2` preserves zero tensor evaluations and spatial block I. The proof also descends from real coefficients to the coordinate field. `alg:necessity`, lines 144–149, gives one finite number of colors avoiding the configuration in every ambient dimension if the tensor condition fails. Used for the symmetrization in the negative argument. Coefficient descent is read to check the exact interface, but the positive construction already lives over the required F.

3. **Sufficiency completion.** [06-groups.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/06-groups.tex), read lines 295–358; Git blob `1e0733089abda7170a5c71b8ba718979be613038`. The final proof obtains equal-endpoint paths with arbitrarily small weight ratio and invokes the path criterion. It explicitly requires no bound uniform in the auxiliary integer n on degrees or number of coordinates. This confirms the qualitative finite-dimensional forcing interface; the review does not infer an effective bound.

4. **Spherical necessity.** [07-consequences.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/07-consequences.tex), read lines 1–290; Git blob `6f66c1027c2f0d18c46d6f822d78eb1fa8733d8a`. `cons:spherical`, lines 8–10, states every finite Euclidean Ramsey set is spherical. Its proof treats the singleton separately, then obtains `||a_i||²+ℓ·a_i+c=0`; the radius is positive for two or more distinct points. Used for the converse.

5. **Independent quadratic rows.** Same source, `cons:quadratic`, lines 62–71, requires a spherical, affinely spanning configuration whose rows `(p_iα p_iβ)_(0≤α,β≤d)` are independent **over F**. Its proof first solves the ordinary sphere linear system over F, then uses an adjugate tensor lift and normalization by a nonzero scalar in F. It does not invert a tensor determinant. Used exactly for all small configurations outside the six-point circle exception. A nonzero minor over F remains nonzero over R, and conversely full row rank over R of a matrix over F is witnessed by a nonzero minor in F. Thus the review's real isotropic-space argument verifies the required field-rank hypothesis.

6. **Strongest directly relevant small-circle consequence.** Same source, `cons:quadrilateral`, lines 106–109, states every nonempty set of at most five distinct circle points is Ramsey. Its proof uses products of two affine line equations to interpolate at five points. `cons:transitive` gives all subsets of finite transitive sets; `cons:nine` gives the generic nine-point obstruction; `cons:twelve` gives a derivation obstruction. Their actual statements and proofs were read as stronger-interface checks. None is a premise for the new six-point lift, and the nine/twelve examples are not substituted for the seven-point boundary.

The only non-elementary mathematical premise needed for the whole reviewed conclusion is the stipulated classification and its listed consequences. Everything new below is finite linear algebra, polynomial algebra, or elementary Euclidean geometry. The full input provenance audit verifies 85 pinned blobs, 199 corpus statement blocks, 19 author read ranges, and 16 primary statement contracts: **215 statement contracts in total**, not 215 corpus blocks plus 16 primary blocks. It also verifies the author's 146-artifact seal. These counts are provenance coverage, not a claim that the reviewer mathematically audited every screened paper.

The Pálvölgyi v1 main theorem is retained as an external comparison: for any transcendental r>2, `{(0,0)} ∪ {(j,±sqrt(j(2r−j))):j∈{1,3,4}}` is a non-Ramsey set on `(x−r)²+y²=r²`. Its actual statement is present in the frozen versioned text and primary contract. The author's note marks appendix material unchecked. **No appendix assertion, or even that external main theorem, is needed for our proof verdict or sharpness:** Section 7 derives the required negative example from the stipulated classification. No current-literature novelty verdict is supplied by R2.

## 3. Audit of the submitted exact local-ring proof

### 3.1 Basis, elimination, and the correct ambient ring

For a characteristic-zero field F and six distinct t_i∈F, set `R=F[U_1,…,U_6]_(U−t)` with residue map ev. A rational expression belongs to R when it has a polynomial denominator nonzero at U=t; this is an algebraic condition, not a real-neighborhood or convergence assertion.

The nine displayed polynomials h_0,…,h_4,a_0,a_1,a_2,J have bidegree at most (2,2). Their independence follows without genericity: their diagonal restrictions separate the five h coefficients, their antisymmetric parts separate the three a coefficients, and J is a nonzero symmetric element vanishing on the diagonal. Equivalently, the independent exact coefficient determinant is 2. Characteristic zero suffices for all factors of 2.

At U=t the first-five h matrix is the ordinary Vandermonde at t_1,…,t_5. Its determinant is nonzero in F, hence its determinant is a unit in R. Therefore H_0^{-1} exists **in R**, and the residual row `ℓ=(-H_6 H_0^{-1},1)` and residuals `r_f=ℓ(f(t_i,U_i))_i` are regular. Residual evaluation is R-linear in the bivariate coefficient vector. It follows that subtracting h columns kills all six evaluations exactly if and only if the residual vanishes.

### 3.2 Fractional-linear family and substitution on the localization

The 3×3 interpolation system has rows `(t_i,1,−t_i U_i)` for i≤3. Its diagonal determinant is `∏_(i<j≤3)(t_j−t_i)`, including the stated sign. The diagonal solution is (a,b,c)=(1,0,0). In fact a,b,c belong to `R_0=F[U_1,U_2,U_3]_(U_1−t_1,U_2−t_2,U_3−t_3)`. The elements ct_i+1 and a−bc have residue 1 and are units. Thus `φ(t_i)=(a t_i+b)/(c t_i+1)` is defined in R_0 and equals U_i for i≤3.

For each partial tail substitution σ_k, begin with the polynomial ring map to R replacing the prescribed tail variables by φ(t_i). If s(U) is an inverted polynomial, then `ev(σ_k(s))=s(t)≠0`, so σ_k(s) is a unit. The universal property of localization therefore extends this map to R. This justifies every denominator substitution, including determinants introduced earlier. It does not assert that an arbitrary numerical Möbius map avoids every denominator zero.

On the fully substituted family, multiply a bidegree-(2,2) restriction by `(cz+1)²`. A monomial x^p y^q becomes `z^p(az+b)^q(cz+1)^(2−q)`, of degree ≤p+2≤4. Over R, the six-value vectors obtained this way form the image of the free rank-five polynomial module R[z]_≤4 under evaluation followed by division by the six units `(ct_i+1)²`. Projection of this image to the first five coordinates is an isomorphism: its matrix is an invertible Vandermonde times an invertible diagonal matrix. The substituted h columns also have invertible first-five matrix, because its determinant has the same nonzero residue as H_0. They are consequently a basis of this module. The sixth value is forced by the first five, and `σ(r_f)=0` holds identically in R.

This argument holds for all nine basis polynomials and then for arbitrary coefficients by linearity, with the coefficients themselves substituted when σ is applied. No finite collection of real evaluations or Zariski-density argument is replacing the module identity.

### 3.3 Divided differences really belong to R

One can make the regularity claim completely algebraic by using the triangular change of variables `v_i=U_i−φ(t_i)` for i=4,5,6 over R_0. It has inverse `U_i=v_i+φ(t_i)` and carries the distinguished maximal ideal to `(U_1−t_1,U_2−t_2,U_3−t_3,v_4,v_5,v_6)`. Tail substitution is exactly setting selected v variables to zero. This is a coordinate change in local polynomial rings, not an implicit-function theorem.

For r=P/s with s a local unit, its difference before and after setting one v variable to zero has denominator equal to the product of the two substituted units. Its numerator vanishes at that variable's zero value and is therefore divisible by that variable in the polynomial ring over R_0 and the other tail variables. Dividing the numerator by v_i leaves an element of R. This proves the regularity of every C_k(r), even at points with v_i=0. Telescoping gives the exact identity `r=Σ C_k(r)v_(k+3)` when σ(r)=0.

In particular `r_a=A v` and `r_J=b v` are identities in R. The proof does not infer ideal membership from tangent-space equality or from formal completion. It proves membership first by substitution and polynomial divisibility.

### 3.4 Jacobian, correction, and six exact equations

Let `H_*(z)=∏(z−t_i)` and `μ_i=H_*'(t_6)/H_*'(t_i)`. All denominators are nonzero constants of F. Lagrange interpolation gives `Σ μ_i t_i^j=0` for j=0,…,4 and μ_6=1. Thus μ is exactly the residual row ℓ at U=t, since those conditions uniquely specify that row.

For f among the a_j and J, all six values f(t_i,t_i) vanish. Differentiating ℓ times the evaluation vector therefore has no contribution from the derivative of ℓ. The k-th derivative is `μ_k ∂_y f(t_k,t_k)`. Since φ depends only on the first three U variables, evaluating a tail divided difference at the base point gives that tail partial derivative. The transverse derivatives are, respectively, `1,2z,z²,0`. This proves both the stated A(t) and b(t)=0, with no sign ambiguity.

Its determinant is `2 μ_4 μ_5 μ_6 (t_5−t_4)(t_6−t_4)(t_6−t_5)≠0`. Hence A is invertible in R and `c=b A^{-1}` belongs to the maximal ideal entrywise. Row/column orientation matters: r_a and v are columns, b and c are rows. Then `r_J=bv=b A^{-1}r_a=c r_a` is exactly the needed identity.

With `f=J−Σ c_j a_j` and `d=H_0^{-1}(f(t_i,U_i))_(i≤5)`, the polynomial `Q=f−Σ d_ℓ h_ℓ` vanishes at the first five pairs by construction and at the sixth by the residual identity. At the base point c=0, f=J, and the five values of f vanish, so d=0. Therefore ev(Q)=J as a bivariate polynomial. This establishes every assertion of Lemma 1, including regularity at the entire prescribed diagonal point for every six distinct elements of F.

## 4. Descent and the circle criterion

Choose a common polynomial denominator Δ for the nine coefficients of Q with Δ(t)≠0. Such a product denominator exists because each coefficient lies in R. Set E=ΔQ. Since F[U] is a domain and maps injectively into its localization R, the six zero evaluation identities for E are identities in **F[U] itself**.

The map `ι:F[U]→F⊗Q F`, sending a∈F to a⊗1 and U_i to 1⊗t_i, is always defined. Algebraic relations among the right t_i merely enlarge its kernel. The construction uses no injectivity of ι. Multiplication composed with ι is exactly evaluation at U=t.

For the coefficient matrix of E, multiply ι(E_αβ) by the single scalar unit `(Δ(t)^{-1}⊗1)`. The tensor evaluations vanish because the six polynomial identities were mapped by a homomorphism. Its multiplied coefficient matrix is J_0 because `E(t;x,y)=Δ(t)(y−x)²`. There is no attempt to invert ι(Δ), which can be a zero divisor. This is the essential distinction from directly mapping the whole local ring to B.

Similarity normalization is legitimate at original scale. If normalized A is Ramsey and the desired set is a translate/orthogonal image of ρA with ρ>0, apply the Ramsey property to the coloring `x↦c(ρx)` in the same ambient dimension, then scale the resulting copy. Its pairwise distances are exactly those of ρA. Congruence absorbs the translation and rotation. No color regularity is used.

Normalize the positive-radius circle to the unit circle and rotate to avoid its one stereographic pole. The inverse parameter `t=a_2/(1+a_1)` and the forward coordinates `(1−t²,2t)/(1+t²)` show equality of the normalized coordinate field with Q(t_1,…,t_6), in both directions. Distinct parameters give distinct points and three distinct circle points are noncollinear, so affine span is R².

For `q=(1,t,t²)^T`, `p=Lq/(1+t²)` with the candidate's rational matrix L, direct multiplication gives `L^T S L=−2J_0`, where S=diag(−1,1,1). Thus `P=−2L^(−T) K L^(−1)` has multiplied matrix S. Its tensor evaluations are zero because the left and right denominators 1+t_i² are nonzero elements of F and yield separate tensor units. This is stronger than the required multiplied spatial block I_2 and meets the source criterion exactly. No transpose, scale, or sign repair is necessary.

## 5. Independent universal polynomial proof: two triple factors

This proof is supplied in full because it is both an independent cross-check and material context for the later contribution assessment. It uses the same six distinct parameters and proves a stronger algebraic statement than local regularity. It is **not** being substituted for an unresolved step of the submitted proof; Sections 3–4 have already verified that proof.

For an ordered triple I=(i_1,i_2,i_3), define over F[U]

`M_I = ((t_i, 1, −t_i U_i))_(i∈I)`, `D_I=det(M_I)`,

`(N_a,N_b,N_c)^T=adj(M_I)(U_i)_(i∈I)`.

Set the bilinear polynomial

`G_I(x,y)=(N_c x+D_I)y−N_a x−N_b`.

The adjugate identity `M_I adj(M_I)=D_I I_3` implies, row by row,

`t_i N_a+N_b−t_i U_i N_c=D_I U_i`.

Hence `G_I(t_i,U_i)=0` for every i∈I as a **polynomial identity**, with no division and no generic-point restriction.

At U=t, put `V_I=∏_(i<j in the ordered triple)(t_j−t_i)`. The matrix has rows `(t_i,1,−t_i²)`, so `D_I(t)=V_I`. The vector (1,0,0)^T solves its right-hand-side system `(t_i)`, and its determinant is nonzero. Therefore the adjugate numerator vector specializes to `(V_I,0,0)^T`. In particular,

`G_I(t;x,y)=V_I(y−x)`.

Take I=(1,2,3) and I'=(4,5,6). Then

`Q_poly(x,y)=G_I(x,y)G_I'(x,y)/(V_I V_I')`

belongs to **F[U_1,…,U_6][x,y]**: its only denominator is a nonzero scalar of F. It has bidegree at most (2,2), vanishes at all six (t_i,U_i), and specializes to `(y−x)²`. This proves the six-pair lemma directly without local denominators, divided differences, or completion.

Mapping its coefficients by `F[U]→F⊗Q F` already produces K with multiplied matrix J_0. Equivalently, map the polynomial numerator and multiply by `(V_I V_I')^(−1)⊗1`. This proof works with arbitrary algebraic dependencies and arbitrary zero divisors of B for exactly the same polynomial-homomorphism reason as Section 4.

The checked-in [factorized_check.py](../experiments/i17_six_point_ramsey_r2/factorized_check.py) independently expands these identities over Q[t_1,…,t_6,U_1,…,U_6]. It checks all six factor evaluations, all six product evaluations, both triple diagonal identities, and the product diagonal identity. All twelve parameters are symbolic; this check is not finite-jet or rational-sample evidence. Distinctness is used only to make V_I V_I' invertible after choosing the actual field. The full universal proof is the adjugate calculation above, independent of software.

**Consequence for handoff:** proof PASS is strengthened, but no substantial-discovery decision follows. The fundamental construction can be expressed as elementary three-point bilinear interpolation followed by multiplication of two factors. Whether applying this to the stipulated classification meets the project's nonroutine threshold is for the separate significance reviewer and parent. This observation must travel with the handoff and must not be hidden behind the longer residual-matrix argument.

## 6. All affine dimensions and all smaller cardinalities

Let A be spherical with 2≤|A|≤6 and choose orthonormal affine coordinates on its affine span. If c is any original sphere center, let c_H be its orthogonal projection to that span. For every a∈A,

`||a−c_H||²=ρ²−dist(c,H)²`.

The right side is the same nonnegative number for every a. It is strictly positive if there are two distinct points, since radius zero would force all points to equal c_H. Thus the resulting configuration meets the sphericity hypothesis in the source's affine-dimensional formulation, without requiring c or ρ to belong to its coordinate field.

Suppose its quadratic evaluation rows are dependent over that coordinate field. Choose any nonzero relation and restrict to its nonzero support, with m≤6 points and affine dimension e. The relation annihilates every polynomial of degree ≤2 on the support. In R^m let W be the evaluation vectors of all affine functions on its affine span; dim W=e+1. With the nonzero relation coefficients λ_i, the form `B(u,v)=Σ λ_i u_i v_i` is nondegenerate. Products of affine functions have degree ≤2, so B|_(W×W)=0. Thus W⊂W^⊥ and

`2(e+1)≤m≤6`.

This argument requires neither positive λ_i nor a positive definite form. Nonzero coefficients on the selected support ensure exactly the nondegeneracy used. Working over R is legitimate because every F-linear relation remains a real relation and the relevant evaluation ranks agree over F and R.

For e=0 the support has one point; for e=1 a line intersects a positive-radius sphere in at most two points. Both contradict the displayed inequality. Hence e=2 and m=6. The whole set A is this support, with six points in an affine plane. Its projected sphere intersection is a positive-radius circle. Section 4 applies.

If the quadratic rows are independent, the actual `cons:quadratic` contract applies directly. The source proof supplies its needed sphere coefficients in F by solving a consistent linear system over F; no unproved assertion about the field of the center or radius is necessary. This covers every other configuration of two through six points. Singletons were already handled directly.

Conversely, `cons:spherical` gives spherical necessity with the stated singleton convention. This proves the candidate's full small-cardinality equivalence and every stated coloring quantifier. There is no use of a “typical position” assumption, and no support smaller than six is accidentally excluded.

## 7. Source-relative seven-point sharpness

Choose seven real parameters algebraically independent over Q. Such a finite choice exists, and in particular all seven are distinct. Their stereographic images affinely span R² and have field F=Q(t_1,…,t_7). Suppose a classification certificate P exists.

Symmetrize using the **tensor flip-transpose**, not ordinary transpose. Its multiplied matrix H is symmetric with spatial block I_2. Multiplying the seven evaluation equations gives

`H_00+2H_01 x_i+2H_02 y_i+1=0`.

Three noncollinear points force the affine polynomial on the left to be identically zero, so H=S=diag(−1,1,1). Thus `K=−L^T P L/2` has multiplied matrix J_0 and has zero tensor evaluations at the seven q(t_i). The latter follows by multiplying by the separate nonzero left/right stereographic denominators before conjugation.

Define a Q-algebra map from the right copy of F to F[[ε]] by `t_i↦t_i+ε t_i³`, while the left copy is constant. Algebraic independence identifies F with the rational function field: for every nonzero polynomial denominator p, substitution has constant term p(t)≠0 and is consequently a unit in F[[ε]]. This proves the field homomorphism exists. The universal property of the tensor product supplies a map `F⊗Q F→F[[ε]]`. It need not be injective; no injectivity is used. Constant-term extraction composed with this map is m.

The image coefficient matrix of K gives `Q_ε=J+εQ_1+ε²Q_2+…`, with every Q_j of bidegree ≤(2,2). Its exact evaluations give `Q_ε(t_i,t_i+εt_i³)=0`. The constant coefficient is J because m(K)=J_0, including the factor −1/2 already checked.

The coefficient of ε is `Q_1(t_i,t_i)=0`. The diagonal restriction has degree ≤4 and seven distinct roots, so is identically zero. The kernel of diagonal restriction on the nine-dimensional bidegree space is the four-dimensional span of J,a_0,a_1,a_2, as the basis proof in Section 3 shows. Accordingly `D(z)=∂_y Q_1(z,z)` has degree ≤2. In particular a higher-degree transverse term has not been discarded without justification.

Since `J(t,t+εt³)=ε²t⁶` exactly, the second-order equations are

`t_i⁶+t_i³ D(t_i)+Q_2(t_i,t_i)=0`.

Let `H_7(z)=∏_(i=1)^7(z−t_i)` and λ_i=1/H_7'(t_i). Lagrange's leading-coefficient identity yields `Σ λ_i t_i^j=0` for j≤5 and `Σ λ_i t_i⁶=1`. The degrees of z³D(z) and Q_2(z,z) are at most 5 and 4, respectively. Multiplying the second-order equations by λ_i and summing gives 1=0. This contradicts the assumed tensor certificate. Source classification therefore makes this seven-point circle set non-Ramsey.

There is no factorial error: Q_2 denotes the coefficient of ε², and J's shifted value is computed exactly. Nor is this an inference of Ramseyness from compatible finite jets. It extracts an impossible **necessary** consequence of an exact putative certificate. The positive half used exact polynomial identities. This negative calculation is a re-proof of a known boundary under the accepted source, not a second finding.

## 8. Adversarial objections and dispositions

1. **Could the local construction live only in a fraction field or completion?** No. Every inverse in the submitted proof has nonzero residue, and each divided difference is an actual local-ring element by polynomial divisibility. The independent triple-factor proof even gives a polynomial solution.
2. **Could a substituted denominator stop being a unit?** Not for any σ_k used here: its base-point value is unchanged. The maps are defined via localization's universal property, not pointwise rational evaluation everywhere.
3. **Could matching tangent spaces falsely imply exact ideal membership?** That inference would be invalid. Here exact membership is obtained first from vanishing under the explicit tail-substitution retraction and telescoping. The derivative calculation is used only to prove a matrix already in R is invertible.
4. **Could C_k fail where v_(k+3)=0?** The displayed fraction has a removable factor in its numerator; cancellation is proved algebraically. Finite diagnostic routines that directly divide by a sampled value do not establish this. The independent three-variable test cancels the expressions before evaluating at the diagonal.
5. **Could algebraic dependencies or zero divisors invalidate descent?** No. Polynomial identities map through arbitrary homomorphisms. Only the left scalar Δ(t) is inverted. A direct map of the entire local ring to B is neither claimed nor needed.
6. **Could coefficient-field normalization invalidate the source theorem?** No. The normalized circle field equals Q(t_1,…,t_6) by explicit inverse formulas. Other affine representatives use their own coordinate fields. Similarity invariance concerns the Ramsey property itself.
7. **Could all-six planar points be an incomplete list of quadratic-rank exceptions?** No. The support argument proves m≥2e+2; sphere intersections eliminate e≤1, and m≤6 forces the entire six-point planar set. It does not presuppose every relation has full support.
8. **Could the higher-dimensional invocation need sphere data in F?** The source proof obtains such data by linear-system descent. Positivity and existence are already supplied by the original real sphere and projection. No square-root closure of F is assumed.
9. **Could the seven-point formal map violate algebraic relations?** This is why the negative example assumes algebraic independence. The positive theorem has no such assumption. Rational-sample moment checks do not purport to construct this homomorphism for rational nodes.
10. **Could the result secretly use unchecked appendix barriers as sufficiency?** No. Their non-obstruction statements are not premises. The positive certificate and source-relative negative argument are both proved independently here.
11. **Does proof PASS settle the nonroutine/significance requirement?** No. The two-triple factorization materially simplifies the bridge and must be assessed in the separate gate. The proof review makes no count recommendation.

No objection requires modifying the candidate's mathematical hypotheses. The singleton and quadratic-degree conventions above are explicit readings of the existing source contract, not repairs or widened assumptions.

## 9. Reproducible exact checks, limitations, and seal

All author programs were executed from isolated unchanged copies in this review's `author-reproduction/` directory. The author's programs and outputs were not modified. Both reproduced output files are byte-identical to the frozen originals:

- 140 exact rational certificate evaluations and 140 diagonal determinant checks, with zero excluded trials in that run.
- Twelve exact series directions, 72 evaluation equations through order seven.

Those are supplementary finite diagnostics. The new independent checks import no author code:

- [independent_checks.py](../experiments/i17_six_point_ramsey_r2/independent_checks.py) checks the basis determinant, all nine universal Möbius weighted-restriction degree identities, the symbolic residual-Jacobian determinant, and the circle congruence factors.
- It constructs the complete submitted residual/divided-difference certificate with fixed nodes `(0,1,−1,2,−2,3)`, first three U values fixed at their nodes, and **three independent formal tail variables** u,v,w. All twelve quotients are regular at `(2,−2,3)`. The exact common denominator simplifies to `Δ=4uv+uw−10u−5vw−2v+12w`, with Δ(2,−2,3)=40. All six cleared polynomial evaluation identities and the diagonal coefficient identity pass. This is a symbolic three-variable slice, not a universal proof for all nodes or all first-three variations; Sections 3 and 5 provide the universal proofs.
- A separate descent stress test uses F=Q(sqrt(2)) and `B≅F[r]/(r²−2)`. For six parameters t_i=i sqrt(2), the dependent-family local certificate `(y−rx/sqrt(2))²` is cleared with `Δ=r+sqrt(2)`. In B, Δ is a nonzero zero divisor, since `(r+sqrt(2))(r−sqrt(2))=0`. Normalizing by the **left** scalar 1/(2sqrt(2)) yields `K=e J_0`, where `e=1/2+r/(2sqrt(2))`. All six tensor evaluation equations and m(K)=J_0 pass. This tests the descent rule with a simpler valid local input on a dependent family; it does not misrepresent that input as the full submitted six-variable Q.
- Seven-node moment checks yield exactly `(0,0,0,0,0,0,1)` for degrees zero through six. The kernel/transverse-degree calculation checks the second-order obstruction. Rank checks give five for six circle points and six for the unit octahedron; these illustrate, but do not replace, the support proof.
- [factorized_check.py](../experiments/i17_six_point_ramsey_r2/factorized_check.py) checks the independent polynomial certificate with **all twelve t and U variables formal**, including expanded factor, product, and diagonal identities. Its result is [factorized-check.json](../experiments/i17_six_point_ramsey_r2/factorized-check.json).

SymPy 1.14.0 and mpmath 1.3.0 are retained as two pinned pure-Python wheels, imported directly without changing a global environment. Their PyPI release SHA-256 identities and retrieval URLs are in `experiments/i17_six_point_ramsey_r2/vendor/manifest.json`. The mathematical arguments do not depend on trusting symbolic output as a proof oracle.

From the project root, reproduce with:

```sh
python frontier/experiments/i17_six_point_ramsey_r2/author-reproduction/diagnostics.py
python frontier/experiments/i17_six_point_ramsey_r2/author-reproduction/series_diagnostics.py
python frontier/experiments/i17_six_point_ramsey_r2/independent_checks.py
python frontier/experiments/i17_six_point_ramsey_r2/factorized_check.py
python frontier/experiments/i17_six_point_ramsey_r2/verify_inputs.py
python frontier/experiments/i17_six_point_ramsey_r2/seal.py --verify
```

[Input verification](../sources/i17_six_point_ramsey_r2/input-verification.json) verifies the frozen candidate hash and line count, all 155 snapshots, the 13,223-entry complete pinned inventory, 85 Git blobs against that inventory and their pinned URLs, 199 corpus statement blocks, 19 author read ranges, 16 primary contracts, ten literature retrievals, nine latest-comparison blobs, the original 146-artifact seal, the review's nine selected statement contracts/four complete reading ranges, the byte-identical author reproductions, and new diagnostic statuses. Historical “latest comparison” files are verified as frozen evidence only; R2 makes no new latest-literature assertion.

[artifact-manifest.json](../sources/i17_six_point_ramsey_r2/artifact-manifest.json) seals the review, its sources, snapshots, scripts, pinned execution dependencies, and diagnostic outputs. Only the seal itself and its derived verification output are excluded. [verification.json](../sources/i17_six_point_ramsey_r2/verification.json) records the final seal result. Live candidate and dependency hashes are compared with the frozen inputs, rather than silently replacing a premise if another task edits a shared file.

**Final disposition: PASS on the entire stated mathematical scope, with no proof repairs.** The polynomial factorization in Section 5 is a fully proved simplification to carry into significance review. No candidate/shared-index edits, agents, staging, commits, pushes, finding numbers, or count changes were performed. Parent integration and the independent significance gate remain separate.
