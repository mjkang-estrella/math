# I314 — full-scope contribution analysis

## 1. Target and disposition

**TECHNICAL**, for the entire strict amplification hierarchy as one nomination. This is a routine-reduction judgment, not a claim that the exact displayed theorem has been located in print. The distinction matters: the matrix hierarchy is genuinely stronger than the accepted R019 fixed-witness obstruction and than the completed I309 scalar deductions. Neither logical strength nor a correct proof automatically demonstrates a substantial new operation.

I authenticated and read all 102 lines of the frozen I312 parent proof, SHA256 `da83fdf48779e56c2c8c694973282ecf61ea14c1134e86b9f48bfed12cc89070`. No replacement proof, modified construction, omitted parameter range or live proof-review result is used. This is an independent contribution review, with a mathematical scope check sufficient to make the reduction reviewable. It does not replace the separately assigned independent proof gate.

For a finite A, use base-first evaluation

    Q[A]=Σ_k A^k⊗Q_k,
    C_d(A)=sup{||Q[A]||: Q∈M_d(C[z]), sup_|z|<=1||Q(z)||<=1}.

There is no bound on deg Q. For every integer r>=2 the nomination requires an explicit finite, unitarily irreducible nilpotent A_r with w(A_r)<=1, C_r(A_r)=2 and C_d(A_r)<2 for every positive integer d<r. The construction's dimension and nilpotence bound must also survive. The theorem is about disk evaluation, not a requirement that every numerical range equal the disk. No optimized dimension or quantitative gap is required.

The standard applied here is the completed I292/I309 distinction: a new bridge or obstruction earns substantiality; parameter specialization, an inherited equality chase and generic compactness do not earn it merely by yielding a useful new formula. I do not increase that threshold because the nomination is elementary, or lower it because there are remaining acceptance slots.

## 2. Actual predecessor operations

Gau–Wu's Theorem 5 weights the two scalar model endpoints by sqrt(2) and 1/sqrt(2), with identity on their orthogonal complement. Its proof gives the factorization establishing numerical radius one and norm-two evaluation. Theorem 8's necessity proof chases equality through the condition-two similarity. Both concern scalar H∞ functions. The whole article was read. [Primary PDF](https://ir.lib.nycu.edu.tw/server/api/core/bitstreams/761cc49b-4b82-4fd4-8748-960e6473e874/content).

The classical matrix model criterion is explicit in Benhida–Fricain–Timotin, Lemma 3.1 and Corollary 3.2: a C00 contraction is reducible precisely when its characteristic function has a constant nontrivial input/output block decomposition, equivalently maps one fixed proper input subspace onto one fixed output subspace on the circle. The definitions/model formulas and the criterion's proofs were read. [Primary PDF](https://nyjm.albany.edu/j/2021/27-62p.pdf).

These are different operations. Gau–Wu alone does not state the all-level matrix theorem. The matrix-model criterion supplies the relevant higher-defect operation. Below I derive the entire target from those operations, including the allegedly new positive-density rigidity, rather than silently treating the scalar statement as matrix-valued.

The finite contractive/inner realization mechanism in Knese, Theorems 2.1 and 3.1 with proofs, was also inspected. I credit realization, positive kernels and polynomial inner factors. A general transfer state is a contraction and does not by itself attain norm two under its own functional calculus. The endpoint weighting below is the specific old operation that makes the present chosen original base extremal. [Primary version](https://arxiv.org/html/1907.13191v2).

## 3. The positive-matrix rigidity is classical model irreducibility

Let Φ be an r-by-r polynomial inner function with Φ(0)=0. Put Θ=zΦ and C=S_Θ on K_Θ=H²(C^r)⊖ΘH²(C^r). The following direct argument also verifies the relevant classical criterion in this exact setting, without relying on an unread general-model proof.

Suppose constant proper nonzero subspaces K,J⊂C^r obey Φ(ζ)K=J for every ζ on the circle. Since Φ(ζ) is unitary, it also maps K^⊥ onto J^⊥. For the corresponding orthogonal projections P_K,P_J,

    P_J Φ(ζ)=Φ(ζ)P_K.

Polynomial continuation gives that identity everywhere, and hence P_J Θ=ΘP_K. The constant multiplication projection P_J on H²(C^r) preserves ΘH²(C^r); being self-adjoint it preserves its orthogonal complement too. It commutes with multiplication by z and therefore reduces C on K_Θ. The induced projection is neither zero nor identity because all constants belong to K_Θ, including the nonzero constants in J and J^⊥. This is exactly the old fixed-subspace-to-reducing-summand operation.

Conversely a reducing projection of C preserves its two defect endpoint spaces. Commutation and cyclicity of constants give constant projections P_J,P_K with P_JΦ=ΦP_K. This converse can also be seen directly from the coefficient pairing in Section 6 below. Thus C is irreducible exactly when Φ has no such proper constant subspace pair.

Now suppose B=B* and D are constant matrices with

    Φ(ζ) B Φ(ζ)*=D.

D is Hermitian and unitarily similar to B. If B is nonscalar, choose a polynomial p selecting a proper nonempty subset of its distinct real eigenvalues. Spectral calculus gives nontrivial orthogonal projections

    P_K=p(B), P_J=p(D),
    Φ(ζ)P_KΦ(ζ)*=P_J.

The preceding criterion makes C reducible. Therefore irreducibility of C forces B=cI and D=cI. Conversely any constant nontrivial block decomposition gives the counterexample B=P_K, D=P_J to this rigidity. **The positive-matrix rigidity in the proposal is equivalent to ordinary matrix-model irreducibility; restricting to B>=0 does not change the equivalence, since projections are positive.**

This comparison neither asserts that a fixed Fourier unitary has scalar commutant nor awards novelty for that false assertion. The relevant operation uses the whole function Φ. The exact positive-density statement is a spectral-projection reformulation of the classical criterion.

For the proposal's explicit Φ, old-criterion irreducibility is verified by elementary separating delays. Set M_j=j, N_j=2^j−1 and U_jk=r^−1/2 exp(2πijk/r), indexed 0 through r−1. Then Φ=zD_MUD_N. If Φ B Φ*=D is constant, its ith diagonal entry contains

    Σ_(k,l) U_ik conjugate(U_il) B_kl z^(N_k−N_l).

All nonzero ordered differences are distinct: if k>l, the positive difference 2^k−2^l has two-adic valuation l and odd part 2^(k−l)−1, determining both indices; negative differences are separated by sign. Every U_ik is nonzero. Consequently B is diagonal. For B=diag(b), constancy of D_M UBU* D_M* and the distinct M_j force UBU* diagonal. Its off-diagonal Fourier modes exhaust the nonzero modes of b, forcing b constant. This verifies classical irreducibility for the explicit delay product. Positivity is unnecessary in this algebraic check.

The operation is the familiar construction of an inner function without a constant block decomposition, by two incompatible diagonalizations separated by distinguishable monomials. The powers of two make a convenient explicit separating set. No optimal size or delay bound is nominated, so their precise growth supplies supporting explicitness rather than an optimization theorem.

## 4. Rank-independent endpoint construction and finite parameters

Here is the matrix version of the scalar Gau–Wu calculation, written rather than presumed. Constants E and ΦC^r=F are orthogonal r-dimensional spaces in H=K_(zΦ). Let G=H⊖(E⊕F). Direct Hardy-space multiplication gives

    ker C*=E, ker C=F,
    C*C=I−P_F, CC*=I−P_E.

Indeed if Cf=0 then zf=Θh, so f=Φh; orthogonality to zΦH² forces h constant. For f⊥F, testing zf against Θh with h=h(0)+zh_1 shows zf∈H. Thus C is an isometry on F^⊥, with range E^⊥. The proof uses endpoint subspaces, not one-dimensional endpoint lines.

Define

    X=2^−1/2 P_E+2^1/2 P_F+P_G, A=XCX^−1,
    B=CX^−1/√2.

Then B*B=P_E+(1/2)P_G, and the range of B lies in E^⊥. Therefore

    2√(I−B*B)B=XCX^−1=A.

For a unit vector v, Cauchy–Schwarz gives

    |<Av,v>|<=2||Bv|| ||√(I−B*B)v||
              =2t√(1−t²)<=1.

Also every matrix Schur multiplier has norm at most one on vector Hardy space, so its compression Q[C] is contractive. Since ||X||||X^−1||=2, ||Q[A]||<=2 at every coefficient size. This is exactly the old scalar endpoint calculation with identity operators on higher-dimensional endpoints; no upstream complete-Crouzeix theorem is needed.

For the explicit delay product, Θ=z²D_MUD_N. Set L=r+2^(r−1). Entries of z^LΘ^−1 have exponents L−2−N_j−M_i>=0. Hence z^LH²⊂ΘH², H consists of polynomials of degree below L, and C^L=A^L=0. The standard orthogonal identity K_(AB)=K_A⊕A K_B, obtained by decomposing H²=K_A⊕AH², applied to the delay factors gives

    dim H=2r+Σ_j M_j+Σ_j N_j
         =r(r+1)/2+2^r−1.

Thus no infinite-dimensional operator or limiting base is substituted. Orthogonality equations in the degree-<L polynomial space and Gram orthogonalization give exact algebraic finite matrices. This preserves the frozen explicitness algorithm, the stated dimension and the nilpotence bound for every r>=2.

For P=Φ^T, let

    x=r^−1/2 Σ_j e_j⊗e_j,
    y=r^−1/2 Σ_j (Φe_j)⊗e_j.

These are unit vectors in E⊗C^r and F⊗C^r. The transpose gives P[C]x=y. Endpoint weighting gives P[A]x=2y. Since Φ^T is unitary on the circle and contractive on the disk, this finite polynomial has disk norm one and C_r(A)=2. This is endpoint matching built into the chosen model, not a compatibility problem on an independently prescribed original matrix.

## 5. Every smaller coefficient size, including a strict supremum gap

Fix an arbitrary positive integer d<r. Let Q be **any** d-by-d Schur function. Nilpotence defines its evaluation by the first L Taylor coefficients. Suppose ||Q[A]||=2. A norming unit vector exists because the base and coefficient spaces are finite-dimensional. Equality in

    Q[A]=(X⊗I_d) Q[C] (X^−1⊗I_d)

forces that vector x into E⊗C^d, and, after normalization, Q[C]x into F⊗C^d with norm one. Represent them by constant r-by-d matrices V,W, each of Hilbert–Schmidt norm one. Equality in multiplication and orthogonal projection forces the uncompressed Hardy product itself to lie in the model space and equal the output:

    V Q(z)^T=Φ(z)W.                         (1)

For |z|<1, transpose preserves operator norm, so

    Φ(z)WW*Φ(z)*<=VV*.                      (2)

At each circle point ζ let z=tζ with t increasing to one. Only Φ must be continuous there; no boundary continuity of Q is assumed. Inequality (2) gives Φ(ζ)WW*Φ(ζ)*<=VV*. Both sides have trace one, so the positive difference is zero:

    Φ(ζ)WW*Φ(ζ)*=VV*.                      (3)

This elementary equality chase is the higher-defect form of the endpoint equality chase, followed by trace saturation of the same contraction. It requires no classification or synthesis of a new channel.

Equation (3) implies

    Φ(ζ) ran W=ran V,
    0<rank W=rank V<=d<r.

The classical criterion in Section 3 therefore produces a nontrivial reducing summand of C, contradicting the explicit inner-function irreducibility. This directly excludes every smaller-size equality witness. Alternatively the positive-matrix reformulation of the same criterion yields WW*=I/r and rank W=r. That stronger density conclusion is not necessary to obtain the hierarchy.

To retain the **supremum** quantifier, consider the Schur unit ball at this fixed d. Cauchy's estimate bounds every Taylor coefficient matrix by one. From any sequence, diagonal subsequences give coefficientwise convergence, and the coefficient bounds give uniform convergence on every compact subdisk. The limit is again Schur. Therefore its first L jets form a compact set, and evaluation at A is continuous on it. The set of evaluations has an attained norm maximum. Sections (1)–(3) exclude maximum two, and the universal bound is two, so its maximum is strictly less than two.

Finally, the polynomial and Schur suprema agree. For a Schur Q, Q(tz) with t<1 extends past the closed disk and is contractive there. Uniform Taylor approximation followed by division by 1+the approximation error gives disk-contractive polynomials converging in the first L jets to Q(tz). Letting t increase to one gives Q[A]. The reverse inclusion is immediate. Thus

    C_d(A)<2 for this arbitrary d<r.

Since d was arbitrary, every smaller level is covered. Since the construction and all steps hold for every integer r>=2, the whole family is covered. No fixed-witness coefficient-compression assumption, finite polynomial degree cap, effective gap or numerical search has entered.

This compactness step is supporting old finite-dimensional analytic machinery, but it has been written explicitly so that exclusion of attained polynomials is not confused with exclusion of the supremum. The reduction would be incomplete without it.

## 6. Unitary irreducibility survives the weighting

A reducing orthogonal projection R for A preserves ker A=F and ker A*=E, because X preserves E,F,G. It therefore commutes with X and consequently with C and C*. Classical irreducibility of C then implies R=0 or I. Conversely reducing projections of C preserve its defect kernels E,F and commute with X, so they also reduce A. Weighting thus preserves the exact irreducibility question in this model.

For completeness, the coefficient version used in the frozen proof supplies the same old criterion directly. Write R|_E=V_0 and R(Φv)=ΦW_0v. Commutation and the joint cyclicity of constants for C give

    V_0Φ(z)=Φ(z)W_0.

Indeed pairing RC^k e=C^kV_0e with Φv yields the kth coefficient identity, since C^ke=P_Hz^ke. On the circle V_0=ΦW_0Φ*, so the separating-delay calculation forces W_0=V_0=cI, c∈{0,1}. Constants are jointly cyclic because their compressed monomials span H. Hence R=cI. No tensor/direct-sum enlargement that would spoil irreducibility is used.

## 7. Why DPW and general hierarchy examples are not the reduction

DPW Theorem 2.3 relates the completely bounded and complete numerical-radius norms of a unital homomorphism. I read the entire eight-page preprint. Its converse uses an arbitrary A∈M_n of norm one with amplified norm near C and forms

    [[C^−1 I_n, (1−C^−2)A], [0, C^−1 I_n]]∈M_(2n).

The resulting numerical-radius witness retains the original n. The operation doubles the coefficient size and does not bound n by one. Thus it provides no all-complete-norms-detected-at-two theorem. Its complete disk upper bound and similarity facts are credited. [Primary PDF](https://www.math.uwaterloo.ca/~krdavids/Preprints/DPWnum_range.pdf).

For a unital bounded homomorphism ρ of the **full one-generator disk algebra**, put T=ρ(z). If ρ is k-contractive for any k>=1, zero padding shows scalar contractivity, hence ||T||<=1. Polynomial density gives ρ(f)=f(T), and the matrix von Neumann dilation inequality gives complete contractivity. This explains the classical one-generator threshold-one collapse. It does not address norms strictly between one and two or first attainment of the sharp upper bound two.

The proposed evaluations are unital homomorphisms with complete norm two. They cannot be scalar contractive, since that would force complete norm one. Dividing ρ by two is neither unital nor multiplicative: (ρ/2)(fg)=ρ(fg)/2, whereas (ρ(f)/2)(ρ(g)/2)=ρ(fg)/4. Nor does scaling the generator preserve the attained endpoint norm. Consequently general k-contractive/non-completely-contractive examples for other algebras cannot be imported by that normalization.

General operator-space maps also need not obey T^k power relations, numerical radius one, finite nilpotence or unitary irreducibility. Without a conversion meeting these conditions they do not prove the present hierarchy. The reduction above makes all of those conversions explicitly within the old weighted matrix model; no generic hierarchy example is invoked.

ACV v3 Lemma 5.1 and Theorem 5.3, with their proofs, provide finite rectangular detection and mutually orthogonal Schmidt families for a minimal extremal. Proposition 5.4 and Theorem 5.5 were also inspected. They do not select a prescribed first detection rank or synthesize the present numerical contraction. The dimension-three equality argument does not extend to the present dimensions. I do not use these results as an unproved level-two collapse or as a direct antecedent for the whole theorem. [Primary version](https://arxiv.org/html/2608.27346v3).

## 8. Comparison with the accepted and completed project work

I read R019, the completed I292 review, its entire 167-line analysis, and the completed I292 parent disposition. R019 constructs an attained matrix polynomial on the fixed old six-dimensional LSS base and uniformly obstructs all constant scalar compressions of that polynomial. It does not assert that every different scalar polynomial misses the supremum. I292 explicitly identified the original-resolvent compatibility equations beyond the old family's defining constraints and distinguished the original matrix from an ordinary contraction realization of its polynomial.

I312 is stronger in quantifiers: its conclusion controls all polynomials at every smaller matrix level. It is not a duplicate of the accepted fixed-witness theorem, and its r=2 case is not dismissed as that theorem's restatement. But its freely chosen original base is **defined** to be the old endpoint-weighted matrix model. The fixed-base compatibility obstruction that supported R019's substantiality is absent here. The matrix equality exclusion is an application of the classical defect-subspace reducibility criterion after the inherited endpoint norm chase. The explicit Fourier/Sidon choice verifies that criterion, rather than constructing a new type of functional-calculus compatibility.

The user subsequently authorized the now-completed I309 review and analysis. Their supplied hashes match and both were read in full. I309 treats E307 as known through Gau–Wu's all-H∞ model theorem, I306 as the scalar-supremum application on an already constructed witness, and Q310 as technical by an explicit residual/endpoint-deletion reduction. I do not infer any verdict for the matrix hierarchy from I309. Its scalar theorem and its quantitative modulus receive no extra nomination here, and I309's older administrative count is superseded by the user's latest fourteen-count update.

## 9. Upstream relevance, verdict, and limits

The pinned OpenAI statements at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. I read the actual direct theorem and the structural/representation statements, plus the full structural companion endpoint-extremal proposition and proof. The latter supplies rational endpoint interpolation on a similar contraction, not this hierarchy by itself. No new external full body or section was retained.

Logical dependence is explicit: Sections 3–6 establish the entire nominated theorem without the recent general complete-Crouzeix upper bound. Its own similarity provides the complete upper bound, and its factorization establishes numerical radius at most one. The result arose from source-driven equality work, but was not previously logically impossible on the classical disk.

My TECHNICAL verdict rests on an actual full reduction: rank-independent old endpoint weighting; classical fixed defect-subspace reducibility (including the positive-matrix formulation); elementary explicit separating delays; and compact Schur jets. It is neither a title-match judgment nor an inference from search absence. The theorem can be useful and stronger than existing accepted project claims while its operations remain a routine synthesis under the stated contribution threshold. No claim that the exact all-level theorem was previously published is made; DUPLICATE would require evidence that I do not have.

The source search is bounded. Holbrook's 1995 scalar/complete polynomial-bound comparison was only available as a publisher abstract; its full proof returned 403. An optional disk-algebra dilation paper also had inconsistent cached extraction and failed live retrieval; its excerpt was not used as a read theorem. The low-dimensional partial-isometry paper was screened only through its introduction and extreme-rank statements, not exhaustively. These limits prohibit global claims that the hierarchy or a related construction never appeared elsewhere. They do not undo the affirmative routine reduction actually written here.

No necessary mathematical repair was identified in checking the contribution-bearing steps. That is not a substitute PASS from the independent I312 proof reviewer, whose live work was not inspected. No subagent, git operation, numerical scan, publication, acceptance edit or shared-index edit was performed. Only the five assigned authored files are produced, with detached final hashes.
