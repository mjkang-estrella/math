# I64 — independent contribution review of CE61

**Verdict: SUBSTANTIAL for the exact CE61 theorem and its paid capped passage.** This recommendation concerns **one** result: dimension-uniform extraction of the complete algebraic coefficient residual from averaged Mills-function curl under a fixed operator-energy cap, including the symmetric bounded-energy repair needed to use that residual. It is not an acceptance decision, an independent proof PASS, or a recommendation to count AR, U, the logarithmic rate, and the repair separately. The independent contribution draft preceded the in-flight I63 update. I subsequently read the full [I63 review](i63-entropy-coefficient-extraction-r2.md), which gives **PASS ORIGINAL WITHOUT REPAIRS** separately for CE61, its repair, and conditional/supporting claims, and replayed its verifier unchanged. That analytic result satisfies the proof dependency of this recommendation; it is not evidence of substantiality. Parent integration remains separate.

The decisive point is a new quantitative comparison between two different compatibility conditions, with both matrix dimension and the number of coefficient matrices growing. Neither the source's exact origin-jet argument nor its three-index derivative calculus supplies that comparison. Classical spectral clipping supplies much of the tail argument; it does not supply the comparison. The proof is elementary in ingredients. I do **not** credit divided differences, simultaneous tensor rotations, fourth-moment truncation, or ordinary tensor projection as inventions. The contribution is their use to establish the previously unpaid, uniform nonlinear-curl-to-polynomial-curl implication for a tensor that is not initially fully symmetric. This is a meaningful closed subproblem of the entropy program even though substantial further problems remain.

All pinned statements and lower proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises here. The original I61, I59, I53, I55, I56 reports and I61 verifier were read in full. Actual source proofs, not just those reports, underlie the comparisons below. The four current ledgers were captured and their current status inspected. Seven findings remain accepted; this review changes no count or shared file.

## 1. The precise result being assessed

For every fixed finite (K\geq0), all (m\geq1), and every family of **(m) real symmetric (m\times m) matrices** (X_r), assume only

\[
 B=\sum_{r=1}^m X_r^2\preceq KI,
 \qquad L(x)=\sum_r x_rX_r,\qquad \mathsf X_{ijr}=(X_r)_{ij}.
\]

Write (\operatorname{Sym}) for orthogonal full cubic symmetrization, (q=\varphi/\Phi(-\cdot)), and

\[
 t=m^{-1}\mathbb E_{\gamma_m}\sum_{i,r<s}
 |(Dq(L)[X_r])_{is}-(Dq(L)[X_s])_{ir}|^2.
\]

CE61 asserts a modulus depending **only on (K)**, vanishing at zero, such that

\[
 m^{-1}\left(\|\mathsf X-\operatorname{Sym}\mathsf X\|_F^2
       +\sum_{r,s}\|[X_r,X_s]\|_F^2\right)\leq\chi_K(t).
\]

The proposed quantitative choice is (C_K/\log(e/t)) for (0<t\leq1/2), with the explicit infimum in I61(12), zero residual at (t=0), and the bound (K+4K^2) elsewhere. There is no density assumption, no (B\approx I), no assumed full tensor symmetry, no commuting basis, and no fixed family size. The second term is the **sum over the whole ordered family**, not a maximum over pairs.

Conditional on the separately audited smooth-source inputs, this gives a closed capped entropy-to-algebraic-residual statement. If (u=\delta/m), I61 has

\[
 t\leq A_Ku,\qquad
 \beta=\|B-I\|_F^2/m\leq 2000u/c_K,
 \qquad\eta=E_X/m\leq\chi_K(A_Ku).
\]

Its repair produces a fully symmetric (Z), (B_Z\preceq4KI), with

\[
 \|Z-X\|_F^2/m\leq26\eta,
 \qquad
 (\|B_Z-I\|_F^2+\sum_{r,s}\|[Z_r,Z_s]\|_F^2)/m
 \leq2\beta+(2+2340K)\eta.
\]

This conclusion has no AR hypothesis. **Turning it into a single orthogonal exponential-product law does have an unpaid AR hypothesis.** The original coefficient cap is also a genuine hypothesis. General source approximation does not establish that cap for approximants.

## 2. Where the comparison is new, and where it is classical

### The local two-observation comparison

At a fixed (x), the source's Daleckii–Krein operation and its convention of rotating all three tensor indices are already available. Use one eigenbasis for (L(x)) and (L(-x)=-L(x)). For one spectral triple, set

\[
 A=\mathsf X_{isr},\quad C=\mathsf X_{irs},\quad
 e_+=\alpha A-\beta C,\quad e_-=\gamma A-\eta C,
\]

where (\alpha=q[\lambda_i,\lambda_s]), (\beta=q[\lambda_i,\lambda_r]), and (\gamma,\eta) are their reflected divided differences. Strict scalar convexity makes (\alpha-\beta) and (\gamma-\eta) have opposite signs. If the three eigenvalues lie in ([-R,R]), positivity and the compact lower bounds on (q',q'') give bounds for **both**

\[
 A-C\quad\hbox{and}\quad
 (\lambda_i+\lambda_s)A-(\lambda_i+\lambda_r)C
\]

by the pair ((e_+,e_-)), with constants depending only on (R). The second expression is the corresponding entry of the curl of (L^2).

This is not just the statement that (Dq(L)) is positive or invertible as an operator on matrices. Curl antisymmetrizes **after** applying that operator to the coefficient tensor. A single observation (\alpha A-\beta C) has the exact nullvector (A=\beta,C=\alpha); it can vanish with (A-C\ne0). Positivity of the whole derivative does not invert this projected measurement. Reflection supplies a second observation with the requisite sign. The argument does not divide by a spectral gap: at coincident eigenvalues the symmetry difference is still controlled and the gap-weighted part vanishes. This matters for arbitrary families, not merely simple-spectrum generic points.

For fully symmetric coefficients the cancellation simplifies to ((\alpha-\beta)A). Assuming that simplification at the start would discard part of CE61's conclusion. Symmetrizing first is also not a free reduction: the nonlinear curl of the symmetrized pencil has not then been controlled. The paired comparison is exactly what permits both symmetry and quadratic compatibility to be recovered without that circular step.

The elimination itself uses elementary two-variable algebra and strict scalar convexity. Its significance is the **uniform coercive implication with these input and output tensors**, not a new scalar inequality. No primary result read in this audit already provides that implication. Bathory’s paired conjugation estimate is an especially close antecedent, compared explicitly in §3; pairing by itself is not novel. I do not claim that reflection is necessary in every possible proof; it is the submitted proof's substantive compatibility comparison.

### The cutoff really is classical in principle

The Gamma companion already proves fourth moment at most (3), spectral clipping with an (R^{-2}) quadratic budget, and a joint left/right spectral-measure commutator argument. The Kadison–Kastler companion has further random-sign fourth-moment clipping, weighted graph norms, and row/column estimates. It would be wrong to call “fourth moments instead of operator-norm concentration” an unprecedented method.

For CE61, however, the object tested against the cutoff is the coefficient tensor, including its input slot. Under (B\preceq KI), that slot need not have a bounded Gram operator: (X_1=I_m,X_2=\cdots=X_m=0) has (B=I_m) but input Gram (\operatorname{diag}(m,0,\ldots,0)). Thus a trace tail estimate tested against a uniformly bounded coefficient Gram matrix does not apply in all slots. A full-spectrum event is also unsuitable: for (X_r=e_re_r^T), (B=I) but

\[
 \Pr(\|L\|_{\rm op}\leq R)=\Pr(|g|\leq R)^m\longrightarrow0
\]

for every fixed (R). Neither fact refutes truncation; they identify the estimates that must be supplied.

I61 supplies them by elementary **operator** Wick bounds (\mathbb EL^2\preceq KI), (\mathbb EL^4\preceq3K^2I). These can be checked directly by expanding the three pairings and bounding the crossing term by row–column Cauchy–Schwarz. Acting on any *fixed* tensor (V), they give

\[
 \mathbb E\|L_jV\|^2\leq K\|V\|^2,
 \qquad \mathbb E\|L_jL_aV\|^2\leq3K^2\|V\|^2.
\]

For different slots, joint functional calculus and (2uv\leq u^2+v^2) reduce the fourth-order bound to the one-slot fourth moments. No dimension or number of slices is introduced. Put (P=1_{[-R,R]}(L)), (\Pi=P^{\otimes3}), (J=(23)), (S=(I-J)X), (Z=(I-J)(L_1+L_2)X). The familiar projection union bound and these moments give

\[
 \mathbb E\|(I-\Pi)S\|^2\leq12K^2m/R^2,
 \qquad\mathbb E\|(I-\Pi)Z\|^2\leq144K^3m/R^2.
\]

The operation “tensorize spectral projections and bound their union” is ordinary. Its deployment on the two recovered compatibility tensors, with operator moments evaluated against fixed (X), is what makes the local comparison usable uniformly. I credit this as the tail implementation of the same bridge, not a second new theorem about noncommutative compactness. In particular, the source Gamma (3/R^2) budget is a real proof-operation antecedent, not merely a paper with a vaguely related title.

### Coefficients, not just a nearby matrix field

Reflection preserves Gaussian measure, and ordering (r,s) doubles the original curl norm; the paired sum is (4mt). The resulting bounds are precisely

\[
 \|S\|^2/m\leq8a_R^{-2}t+12K^2/R^2,
 \quad \mathbb E\|Z\|^2/m\leq4M_Rt+144K^3/R^2.
\]

The passage from this polynomial curl to the coefficient conclusion is finite algebra. With the **vector** convention (S_{rs}=X_re_s-X_se_r),

\[
 Z_{\cdot rs}=[X_r,X_s]x+
 \sum_t x_t(X_rS_{ts}-X_sS_{tr}+X_tS_{rs}).
\]

Gaussian orthogonality and the family cap bound the three error arrays by (K\|S\|^2) each. Together with (\|X-\operatorname{Sym}X\|^2=\|S\|^2/3), this produces I61's full residual. These final algebraic operations are technical. The conclusion nevertheless does something the pre-existing Hodge projection does not: it controls the coefficients of the *original pencil* and their commutators, rather than only distance of the nonlinear field to some gradient.

The logarithmic optimization and the strict quantitative Mills estimates are also technical once these inequalities hold. Absence of the exact logarithmic statement from the literature is not the basis for the verdict.

## 3. Primary comparison contracts

The source paths and precise read ranges are frozen in `read-contracts.json` and `passages.json`. References to the OpenAI manuscripts in this section mean the immutable pinned versions, not a current branch. Fresh external response bytes and served versions are in the literature manifests, including the late Bathory follow-up. External statements are compared within their actual hypotheses; none is declared a new stipulated premise.

**Entropy manuscript, `rigidity.tex`, `transport.tex`, `matrix.tex`, scalar/certificate/approximation companions.** Assumptions: the normalized smooth transport setting, exact equality for rigidity; the transport derivative tensor is already fully symmetric because it is a third derivative. Conclusion: exact product rigidity via the first two origin jets, the matrix/scalar inequality, and approximation of laws. Available operations: (q)-divided differences, pointwise simultaneous rotation of all three derivative indices without differentiating eigenvectors, positive compact scalar weights, first-chaos/energy bookkeeping, forward Frobenius contraction. Missing bridge: averaged curl of (q(L)) does not control its jets at zero in growing dimension, and the source does not give the paired comparison for a partially symmetric coefficient tensor. Replacing exact zero by small Gaussian (L^2) norm is the issue. The positive lower bound on the normalization matrix and the H1 remainders are useful technical inputs, not CE's contribution. [Pinned rigidity](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/build/manuscript/rigidity.tex), [pinned transport](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/build/manuscript/transport.tex).

**Mahler manuscript, `06-linear-equality.tex`, with `02-projections.tex` and `09-consequences.tex`.** Assumptions: its normalized linear field and the scalar profile deficit arising from the Mahler proof. The proof constructs the positive two-point measure

\[
 \nu[\Psi]=m^{-1}\mathbb E\sum_{\ell,i,j}|(M_\ell)_{ij}|^2\Psi(\lambda_i,\lambda_j)
\]

and identifies (\nu[(a-b)^2]=m^{-1}\sum_{\ell,k}\|[M_k,M_\ell]\|^2). Scalar profile separation forces diagonal support at equality. Available operations: spectral-measure scalarization, nonnegative weighted off-diagonal coercivity, Gaussian coefficient extraction, continuous divided differences. These are close antecedents of CE's second half. Missing bridge: CE's input is a **difference of two derivative entries**, not a supplied positive scalar-profile integral; its coefficients can cancel. The displayed measure cannot simply be assigned CE's deficit. The paired two-observation estimate is the needed reduction to positive squares, and also pays the absent full symmetry. Neither the projection normalization nor the consequences section provides it. This is an operation-level mismatch, not just a different theorem title or deficit name. [Pinned proof](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/build/sections/06-linear-equality.tex).

**Tracial projection/Gamma manuscript, §10, including the whole fourth-moment and clipping proofs.** Assumptions: the manuscript's unital tracial setting, averaged centered symmetries and a selfadjoint observable; contraction test elements. Conclusion: moments normalized through order two, fourth moment bounded by (3), clipping errors of orders (R^{-3}) and (R^{-2}), and non-increase of tracial commutators under scalar Lipschitz clipping. Available operation: control loss by moments rather than a rare operator-norm event; two commuting spectral slot operators already occur as left/right multiplication on tracial (L^2). Missing bridge: no nonlinear curl comparison and no partially symmetric three-index coefficient family. Its trace estimate does not by itself imply the operator-valued Wick bound against an uncapped input Gram. That additional bound is an elementary row–column calculation, not a separate substantial invention. [Pinned §10](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Tracial-projection-methods-and-uniform-property-Gamma-September-23-2026/build/sections/10_unital_averaging.tex).

**Additional corpus operator-algebra companions.** The universal strong Kadison–Kastler manuscript's foundations use closeness in cb norm to an existing representation and an associative product; its amplification/finite/modular sections explicitly use clipping, row–column estimates, random-sign fourth moments, and weighted signal retention. These reinforce the classical status of the tail method. They do not start with CE's averaged nonlinear curl. The near-inclusion manuscript's common-corner/polar argument assumes commuting ambient algebras and an operator-norm near inclusion; it cannot manufacture a commuting algebra from CE's hypotheses. The higher bounded Hochschild manuscript's normal-map (L^2) continuity is on a fixed bounded algebra ball; it supplies neither the needed uniform modulus over varying families nor an approximate multiplication with CE's norm. The weak-MTW spectral comparison concerns Jacobi fields on a fixed compact Riemannian manifold. These were inspected as actual proof passages, not imported by keyword.

**Daleckii–Krein / functional calculus.** Tropp's *Matrix Analysis*, captured 2022 lecture notes, Theorem 14.13, gives (Df(\Lambda)H=f^{[1]}(\Lambda)\circ H) for (C^1) scalar (f) on an interval and Hermitian matrices, with orthogonal/unitary conjugation for general matrices. This applies directly to each real symmetric slice and is fully credited. It supplies the four coefficients in the two scalar equations, not coercivity after tensor antisymmetrization. A bounded primary search for quantitative integrability/Hessian compatibility/operator-function coercivity found no theorem with that latter conclusion. The Manchester Noferini primary PDF request timed out; no unseen theorem from it is used. [Tropp notes](https://www.tropp.caltech.edu/notes/Tro22-Matrix-Analysis-LN.pdf).

**Closer nonlinear functional-calculus antecedents: Bathory.** The served arXiv:2505.07987v3, *Commutator calculus and symbolic differentiation of matrix functions*, Theorem 3.1 and its proof, gives coordinate-free divided-difference calculus. Section 4.2, equation (4.4) and its derivation, explicitly writes a power-gradient inequality's surplus as a positive weighted commutator square; (4.6) treats general nondecreasing functions. Thus nonlinear derivative coercivity and spectral commutator remainders are already available concepts. The missing input is a bound on that **full-gradient surplus** by CE's antisymmetrized curl; substituting (B=q(L)) or (e^L) does not establish one. [Primary v3](https://arxiv.org/abs/2505.07987v3).

Bathory's published 2022 *Sharp nonlinear estimates for multiplying derivatives of positive definite tensor fields*, Theorems 1–2/Lemma 1 and their full proofs, is closer still to the pairing idea. For (P(s)=\int_0^1 B^{(1+s)v}HB^{-(1+s)v}dv), it proves \(\langle P(s),P(-s)\rangle\geq\|P(0)\|^2\) by an even scalar function whose second derivative is a conjugated commutator square. This already uses reflection and positivity to compare nonlinear matrix derivatives. It acts on the **same whole matrix (H)** in a Frobenius inner product. CE instead observes two differences of tensor entries, with different spectral multipliers on (A,C); antisymmetrization does not commute with these multipliers. The known paired inner-product inequality cannot be pushed through that projection without another argument. CE's two-equation elimination supplies that argument for its particular projected measurements. I therefore credit neither reflection in general nor positive commutator remainders as new, and retain the narrower compatibility-bridge verdict. [Published primary PDF](https://files.ele-math.com/articles/mia-25-48.pdf).

**Matrix Gaussian moments.** Tropp, *Second-Order Matrix Concentration Inequalities*, captured author preprint, Proposition 2.3 and §§6–7, treats a Hermitian Gaussian series with matrix variance (\sum H_i^2). The Schatten moment inequality is count independent; its operator-norm consequence incurs a logarithm of matrix dimension. These are classical moment tools. CE's fourth *operator* moment is more directly obtained by its finite Wick expansion than by replacing a trace bound with a false operator bound. The literature therefore pays for the moment methodology, without paying the nonlinear compatibility implication. [Author preprint](https://tropp.caltech.edu/papers/Tro16-Second-Order-Matrix-preprint.pdf).

**Hodge and incompatible-tensor estimates.** Yang, arXiv:1111.1295, served v1, §2/Theorem 2.1 and the chaos argument, records the Gaussian Weitzenböck identity (\Delta_q=N+q) and exact/coexact decomposition on abstract Wiener space. This is an explicitly dimension-independent antecedent, not a dimension-dependent estimate dismissed by name. It supplies the row-gradient projection used in I59, but its output is an arbitrary gradient field; applying nonlinear inverse functional calculus does not preserve compatibility or a linear pencil. Neff–Pauly–Witsch, arXiv:1302.2661, served v2, Theorem 1, controls a tensor field by its symmetric part and row curl on an admissible bounded domain with boundary or skew-kernel conditions. Its constants depend on the Korn/Maxwell domain constants; applying it to a symmetric (q(L)) leaves its entire symmetric part on the right. It does not estimate CE's coefficient residual by curl alone. [Yang](https://arxiv.org/abs/1111.1295), [Neff–Pauly–Witsch](https://arxiv.org/abs/1302.2661).

**Almost commuting families.** Filonov–Kachkovskiy, arXiv:1008.4002v2, Theorems 2–3 and their block construction, give normalized Hilbert–Schmidt approximation for selfadjoint contractions: pair exponent (1/4), family exponent (1/4^{N-1}) and a count-dependent threshold. Bansil–Kachkovskiy, arXiv:2608.31000v1, Theorem 1.1 improves the pair distance power to (1/3), with ([X',X]=0); Theorem 1.3's proof explicitly sums the other (N) matrices and loses (\sqrt N), and Corollary 1.4 has squared-distance power (2/3^{N-1}) with (C(N)). Their proofs were read, including spectral partitions and the final averaging step, not merely abstracts. They assume small commutators, which CE is tasked with extracting. They also do not supply a uniform-in-(N=m) linked symmetric algebra rounding theorem. Neither realification nor individual application to pairs removes those two issues. [FK](https://arxiv.org/abs/1008.4002), [BK](https://arxiv.org/abs/2608.31000).

**Tensor tangent and exact algebra structure.** Published Biaggi–Draisma–Seynnaeve Proposition 4.1 and Robeva Lemma 3.7 provide the odeco tangent equations. BDHR arXiv:1512.08031v1, Lemmas 10–11/Proposition 12, provides exact real positive-inner-product associativity structure. These operations are fully credited in I56's concrete reduction of H53. They require exact identities or a local neighborhood and do not extract them from averaged curl. The I56 transverse derivative (2) and estimate (R(T)\geq2d-\sqrt5d^2) have a **total-distance** entrance. Dividing by (\sqrt m) does not make that entrance uniform in normalized distance. Auddy–Yuan arXiv:2007.09024v2, Theorems 2.4/3.1 and the actual polar proof, assume odeco tensors or supplied factors with singular values in ([1-\delta,1+\delta]). CE has no such factors. [Published BDS](https://rendiconti.dmi.units.it/volumi/54/017.pdf), [Robeva](https://arxiv.org/abs/1409.6685), [BDHR](https://arxiv.org/abs/1512.08031), [Auddy–Yuan](https://arxiv.org/abs/2007.09024).

**Approximate C*-algebras and Frobenius algebras.** Kitaev arXiv:2405.02434v2, Definition 2.1/Theorem 2.3, assumes uniformly small multiplicative/associative defects in Banach norm, and the channel construction assumes cb almost-idempotence. Its conclusion is an abstract C*-algebra and encoding/decoding, not a normalized-superoperator-HS dephasing theorem. The paper itself gives a non-CP spectral-projection example. Coecke–Pavlovic–Vicary arXiv:0810.0812v1, Theorem 5.1/§6, identifies **exact** commutative dagger Frobenius monoids with orthogonal bases, special ones with orthonormal bases. Poinsot's captured revised author paper, §3.4/Corollary 3.6, has approximate *units* for exact associative Hilbertian Frobenius algebras; it does not allow approximate multiplication. None closes AR, much less derives its hypotheses from CE's analytic input. [Kitaev](https://arxiv.org/abs/2405.02434), [CPV](https://arxiv.org/abs/0810.0812), [Poinsot](https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf).

**Entropy/cone external antecedents.** Fradelizi–Marín Sola arXiv:2406.07406v1, Proposition 5.2 and Lemma 5.2 with their cone computations, transfers strong slicing formulations and computes cone covariance. The captured published-author Melbourne–Nayar–Roberto paper, Theorem 1.1 and §§3.1–3.3, proves the scalar entropy extremum through decreasing rearrangement and two-piece log-affine reduction. Neither has a matrix-pencil compatibility estimate or a globally aligned growing-dimensional near-extremizer theorem. The accessible FMS preprint is the comparison; this review does not claim to have obtained its final journal proof. [FMS](https://arxiv.org/abs/2406.07406), [MNR author PDF](https://perso.pages.math.cnrs.fr/users/cyril.roberto/Articles/Melbourne-Nayar-Roberto.pdf).

## 4. The repair is a technical part of the same candidate

De Lathauwer–De Moor–Vandewalle, *A Multilinear Singular Value Decomposition*, SIAM J. Matrix Anal. Appl. 21 (2000), Property 10 and its proof, bounds the error of multilinear spectral projection by the sum of discarded mode energies. Its proof is a union bound on squared core entries. CE's repair uses precisely that ordinary projection operation, with the same projector in all slots to preserve full symmetry. It discards *large* singular directions, so the usual low-rank optimality wording is not its application; the underlying orthogonal-projection error bound is identical. [Primary PDF](https://www.math.ucdavis.edu/~saito/data/tensor/lathauwer-etal_mulilinear-SVD.pdf).

Here is the complete technical reduction, including the mass budget often missing in a rank-only argument. Let (T=\operatorname{Sym}X), (e=\|T-X\|_F), (M_X) its first flattening, and (P=1_{[0,4K]}(B_T)). Matrix symmetry gives (M_XM_X^*=B_X\preceq KI). For (k=\operatorname{rank}(I-P)), (a=\|(I-P)M_T\|_F),

\[
 2\sqrt{Kk}\leq a\leq e+\sqrt{Kk},\quad a\leq2e.
\]

The projection error satisfies (\|T-P^{\otimes3}T\|_F^2\leq3a^2\leq12e^2). The new first flattening is (PM_T(P\otimes P)), giving the (4K) energy cap; the triangle inequality gives (26e^2) distance to (X). The elementary Gram perturbation inequality with operator norms (2\sqrt K,\sqrt K) gives (234Ke^2), and expansion of the two commutators with the family cap gives (936Ke^2). The final residual bound follows by squaring the sums against (B_X-I) and the original commutators. This pays all three slots without ever assuming the input flattening of (X) is capped.

Thus I61's repair is useful and correctly targeted, conditional on the proof review, but **TECHNICAL as an operation**. It repairs heavy coefficients created by symmetrizing an already capped tensor. The original I59 heavy star is outside the fixed-(K) premise. It cannot be advertised as a solution to that obstruction.

## 5. General scalar functions and the strongest technical-only objection

The proof extends to smooth scalar (f) with (0<f'\leq1) and (f''>0), using compact constants (a_R,h_R). The (1)-Lipschitz assumption ensures finite averaged derivative energy; reflection need not make (f) odd or even. The same paired elimination, moments, and coefficient identity give a modulus uniform in dimension for each fixed (f,K). They do not give the Mills logarithmic rate without quantitative information on those compact constants. Affine (f) does not qualify: a fully symmetric nonassociative cubic has zero curl for affine (f(L)), while its commutators can be nonzero.

This generalization makes clear that Gaussian-tail IFR is not the conceptual novelty. It is a convenient elementary verification for the source's particular (q). The standard derivative lemma supplies the general class's divided differences, but still not their antisymmetrized two-observation coercivity. No read primary lemma immediately supplies CE for this entire class.

The strongest objection is fair: once the two scalar equations are written down, their elimination is elementary, and after that the source/classical clipping method and finite coefficient algebra finish the proof. I agree with that description of the ingredients. I do not infer substantiality from length, difficulty, or the search failing to find the exact statement. The reason to retain a substantial verdict is that this combination establishes a **uniform implication not present in any paid interface**, on the exact analytic quantity already controlled by the entropy source, for an unrestricted growing family with initially missing symmetry. It replaces origin-jet extraction whose constants deteriorate with (m), rather than optimizing a constant or restating an already available uniform transfer.

Concretely, it says that every sequence with a common cap (K), dimensions (m_j\to\infty), and normalized Gaussian curl tending to zero has normalized *total* coefficient residual tending to zero. That permits total residuals that are unbounded, so fixed-dimensional compactness or a small-total-error tubular theorem does not supply it. It also produces the bounded-energy symmetric input for the separate algebra-rounding problem. This is why the result crosses a substantive interface in the program even without solving that next problem. A complete technical reduction could certainly derive the comparison from older operations; it need not find the identical theorem printed elsewhere. The reductions actually supplied by the read antecedents leave the projected-cancellation problem to be solved. I regard its solution, with the stated uniform payoff, as substantive theorem-level progress. I do not claim a new calculus or rule out a shorter elementary proof.

This judgment is narrower than claiming an indispensable method in all proofs, a new general theory of operator compactness, or a solved entropy stability conjecture. The abstract coefficient theorem itself can be formulated without assuming the entropy inequality; its **new upstream-enabled payoff** is the capped reduction of near equality in the pinned sharp entropy theorem to normalized algebraic residual. That application, and the supplied scalar (q)/compatible transport framework, connect the standalone theorem to the user's significant problem.

## 6. Scope boundaries and correctness separation

No material proof concern found during this contribution review requires changing the claimed scope. The completed I63 review separately passes the original paired coercivity, correlated operator-slot tails, coefficient identity and constants, repair, and capped entropy inputs without changes. Its details expressly handle coincident eigenvalues, a potentially negative Wick crossing term, the moving polynomial tensor by keeping the original tensor fixed, and the uncapped input Gram. I read these details after drafting the independent contribution judgment. This report remains the contribution gate; the numerical and provenance PASS below is not itself an analytic PASS.

AR remains unproved and unrefuted, including the exact (B=I) case. The generic rank-(m) CP projection countermodel has no linked real symmetric cubic realization and is not an AR counterexample. The harmonic-block dilution example obstructs substituting cb defect for normalized superoperator Hilbert–Schmidt defect; it also does not refute AR. Local variational deflation identities leave adaptive energy charges and the small-(c) branch unpaid. None is nominated separately.

U remains unproved and unrefuted. CE's logarithmic coefficient modulus is not the proposed square-root law-distance rate. Heavy original directions, symmetry-preserving normalization, and a single global orientation remain substantive interfaces. Conditional entropy deficits cannot be summed as a nonnegative budget: the negative log-scale terms in the rotated exponential example must remain. I59's heavy star is not a realized density counterexample. Chosen-orientation exact coupling costs bound the orbit infimum; I59's quadrature does not certify upper bounds, and its (m=512) nonconvergence is retained. No uniform coefficient cap is inferred from approximation of laws.

I55's original-proof PASS for H53 and I56's TECHNICAL ONLY verdict are consistent: the latter supplies an actual old tangent/nearest-orbit reduction of the same fixed-dimensional theorem. CE61's change of quantifier is not enough on its own; it is supported here by the explicit comparison and tail analysis in §2 and the absence of a paid replacement in the contracts. Nothing in this review revives H53 or nominates the Hodge/polar/H1 input work.

## 7. Evidence and bounded-search limits

The [evidence directory](../sources/i64_entropy_coefficient_extraction_novelty/) freezes this full assignment, 15 initial inputs plus three I63 dependency inputs, the complete 13,223-entry tree/749-manuscript inventory, and all 9,340 ignored-corpus files by SHA-256 and pinned Git blob. Searches use `rg --no-ignore` on that fixed corpus and retain **line multisets**, not output-order hashes. The three search families cover nonlinear compatibility/divided differences, moments/clipping, and almost commuting/approximate algebra/tensor rounding; their counts are 99, 311, 25. All manuscript names were inventoried; this is not a claim to have read all 749 manuscripts. The selected proof passages and full-read contracts identify the actual depth of reading. Broad title/hash coverage is provenance, not the novelty argument.

Fresh primary retrieval made 36 requests: 35 succeeded, including four immutable raw-source responses; one Noferini PDF request timed out. Served arXiv versions, HTTP metadata, exact bytes and extracted PDF text are retained. The supplemental HOSVD, Gaussian Hodge, Korn, and two Bathory sources were retrieved independently in this round. There are 20 PDF text replays, 49 read contracts and 62 exact passages, and 26 selected pinned source files. The manifests preserve both successful and failed requests. Bounded search terms, exclusions and the distinction between search discoveries and read proofs are in `search-notes.md`. This is not worldwide priority certification. No MathDB score or ranking is invented.

The read-only I61 verifier replay passed unchanged: 110 sealed artifacts, 14 inputs, 19 pins, 339 prior files, eight prior brief copies, 9,340 corpus files, 37 passages, 30 contracts, 27 primary responses, 13 PDF replays, 4,640 exact assertions and ten floating records. It reports the four mutable ledger drifts. Its output is saved as `i61-readonly-replay.json`; no prior seal was refreshed. I64 additionally hash-references 450 existing prior evidence files without recursively copying their archives. The later I63 replay also passed unchanged: 102 sealed artifacts, 33,917 exact assertions and 29 labeled floating records; its full output is `i63-readonly-replay.json`. The three late frozen dependency inputs are I63’s report, verifier and seal. The user’s in-flight message is preserved separately.

The independent [I64 diagnostics](../experiments/i64_entropy_coefficient_extraction_novelty/diagnostics.py) contain 18,051 exact rational assertions: compact divided-difference tests for a convex polynomial, explicit single-observation cancellation/reflected noncancellation, full coefficient identities for nine real symmetric families in dimensions 2–4, Wick expansion and principal-minor checks of the fourth operator bound, and exact large-input-Gram/symmetrization-cut examples. These are finite consistency checks, not proof of a universal modulus. They deliberately do not reuse the author's diagnostic module. No floating diagnostic is represented as certification. Initial optional-dependency attempts failed; the final implementation uses the standard library only. An initial checker used the tensor-slot order where the polynomial identity requires the vector (S_{rs}) order; the corrected convention and failed attempt are recorded in `work-log.md`. This was a checker error, not an alteration of I61.

Run from the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i64_entropy_coefficient_extraction_novelty/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i64_entropy_coefficient_extraction_novelty/verify.py
```

The I64 verifier checks its own seal, immutable inputs and pins, complete corpus/tree inventory, search line multisets, old evidence hashes, fresh primary responses and PDF text replays, passage slices, read contracts, and deterministic diagnostics. It reports mutable-ledger drift separately. It does not settle analytic correctness or priority. Only assigned I64 paths were written; no agents, staging, commits, publishing, shared edits, count changes, or old-seal refresh occurred.
