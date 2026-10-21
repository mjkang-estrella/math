# Arithmetic r138 — prefreeze working derivations

Status: PREFREEZE feasibility work; no frozen theorem and no author-proof nominee. Codex / GPT-6 Astra / high / default service tier. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and every operative upstream proof are premises stipulated true. These calculations concern applicability and additional operations, not upstream correctness. Parent alone assesses contribution, correctness, acceptance and count.

## 1. What the integrated source already supplies

Write D for the field manuscript and ID for the integral manuscript in SOURCE203. The entire 23-object TeX/Bib family was read before these notes. D proves full Donovan finiteness at every prime and bounded defect order, including nonabelian defects and p=2. ID proves the integral assertion over Witt vectors and each fixed complete mixed-characteristic DVR with algebraically closed residue field, including ramified rings. A finite list, its base changes, bounds obtained by taking a maximum over it, and routine Morita invariants are already consequences of that premise.

The mechanisms matter more than the final list. D combines bounded projective row projections, fixed-root geometric bounds, rank/weight reduction, rational marked Jordan diagrams, factorial-normalized projective-cone transport, and cuspidal triangle endpoints. In particular the runner/cohook maps transport projective-character cones; they do not assert Morita equivalences to groups of bounded order. Their nonzero small error terms suffice for cone-volume/Cartan bounds. They cannot simply be read as a categorical stopping rule.

For extensions, actual conjugation factors n(s,t) survive the partial regular embedding and dual recovery. The regular overgroup may have an unbounded central cover; the construction descends that cover before imposing defect bounds. Based Frobenius comparisons are aligned by finite integral Picard groups, and then corrected by units. Field Lang descent acts on the based data, not merely on the unlabelled algebra. In ID, comparison discrepancies are specifically Teichmüller p-prime roots, rather than arbitrary integral units. The induced progenerator and its endomorphisms retain the full factor identity. The Sylow crossed product is realized as a genuine group block, its total orders enter a finite list, and the HH¹=0 grading argument retains labels/markings. Finally a p-prime kernel is split, matrix determinants force the remaining Sylow scalar defect into Teichmüller roots, and restriction on principal-unit cohomology is injective by transfer. This closes the integral extension problem already.

In primary literature, Farrell–Kessar's actual characteristic-zero linear twists and central-quotient descent pay the quasisimple rationality interface; Eaton–Eisele–Livesey (EEL) pay integral Lang descent and bounded-colength order finiteness; Eisele's geometry pays finite rigid lattices/Picard groups; Eisele's published Picard paper pays finite-truncation recovery of outer automorphisms and p-prime crossed-product finiteness. Its published Corollary 4.9 has the p-prime hypothesis. ID supplies the missing mixed p-part operation for the actual block extensions. Repeating that improvement is not a new operation here.

## 2. A completely explicit correction for close based factor systems

This is a feasibility calculation, not a distinct discovery nominee. It is useful because it tests the finite-precision direction through all of the action/factor/base-change compatibility, rather than stopping with the phrase “principal-unit obstruction.”

Let O be ANY complete mixed-characteristic DVR, p its residue characteristic, R a finite free O-algebra with separable generic algebra A=Frac(O)⊗R, and Q any finite group. No splitting or algebraic-closure assumption is needed for this calculation. Fix a separability element

    e = Σ_i x_i ⊗ y_i ∈ A ⊗_K A^op,
    Σ_i x_i y_i = 1,
    Σ_i a x_i ⊗ y_i = Σ_i x_i ⊗ y_i a  (a∈A).

Choose an integer h≥0 such that p^h e∈R⊗_O R^op. This is supplied numerical input, obtained by clearing the finitely many denominators of e. Put a=v_p(|Q|) and c=1 for odd p, c=2 for p=2. All depths below are powers of p, not powers of a uniformizer; the same formula therefore works for arbitrarily ramified O.

Consider two normalized based factor systems (α,f), (α',f') on the SAME R,Q. Thus α_gα_t=ad(f(g,t))α_gt and

    f(g,t) f(gt,u) = α_g(f(t,u)) f(g,tu).

Assume that α'_g−α_g maps R into p^N R and f'(g,t)−f(g,t)∈p^N R for all indices, with

    N ≥ h+a+c.

The following gives the actual change of homogeneous units, not just equality of outer actions.

### 2.1 Exact inner correction with controlled denominator

Set θ_g=α'_g α_g^{-1}; it is congruent to identity modulo p^N. Define

    w_g = Σ_i θ_g(x_i)y_i.

Applying θ_g on the first tensor factor to the centralizing identity for e gives

    θ_g(r)w_g = w_g r   (r∈R).

Writing p^h e as a sum of integral tensors shows w_g−1∈p^(N−h)R. Since N−h≥1, w_g is a unit. Consequently θ_g=ad(w_g), exactly. With normalized data w_1=1. This proof works for nonsplit generic algebras as well.

Gauge the first factor system by w:

    f^w(g,t)=w_g α_g(w_t) f(g,t) w_gt^{-1}.

Its action is α', and f^w−f∈p^(N−h)R. Therefore

    z(g,t)=f'(g,t) f^w(g,t)^{-1}

is central, is a normalized 2-cocycle for the genuine Q-action induced by α' on Z(R), and belongs to 1+p^(N−h)Z(R). Centrality follows because f' and f^w implement the same pair of automorphisms. The depth assertion uses saturation: if p^m r is central, torsion-freeness of R implies r is central.

### 2.2 Correct the central cocycle, including the wild part

For any finite free commutative O-algebra Z, log and exp are inverse group isomorphisms between 1+p^c Z and p^c Z with c as above. They converge by v_p(n!)≤(n−1)/(p−1) and v_p(n)≤n−1; the usual stronger inequality at c=2 handles p=2. These are identities of convergent commutative power series and commute with O-algebra automorphisms. Z(R) is finite free and complete, so they apply here even if the center is nonmaximal or has zero divisors.

Let b(g,t)=log z(g,t)∈p^(N−h)Z(R). Its additive cocycle identity is

    g·b(t,u) − b(gt,u) + b(g,tu) − b(g,t) = 0.

Set B(g)=Σ_{u∈Q} b(g,u). Summing the identity over u, with tu permuting Q, gives

    g·B(t) − B(gt) + B(g) = |Q| b(g,t).

Thus t(g)=B(g)/|Q| belongs to p^(N−h−a)Z(R), and δt=b. Define q_g=exp(t(g)). Then δq=z. Set v_g=q_g w_g. We obtain the exact two identities

    α'_g = ad(v_g) α_g,
    f'(g,t)=v_g α_g(v_t) f(g,t) v_gt^{-1},

with v_g∈1+p^(N−h−a)R and v_1=1. The graded map from the primed crossed product to the unprimed one is

    r u'_g ↦ r v_g u_g.

The displayed identities verify both multiplication with R and multiplication of every pair of homogeneous generators. The map is a bijection because each v_g is a unit. It fixes R and fixes all degree labels.

### 2.3 Base change and the precise information this buys

For a flat continuous local map O→O' of complete mixed-characteristic DVRs, e⊗1 is still a separability element and the same p^h clears its denominators. The formulas w,B/|Q|,log,exp commute with the map; the corrected equivalence therefore base changes as an actual based graded isomorphism. Center formation commutes with flat base change here: it is the kernel of finitely many O-linear commutators. No uniformizer has been silently identified across a ramified extension.

This proves injectivity of reduction on based factor-system classes at a specified depth when the representatives themselves agree in coordinates at that depth. More generally a based graded isomorphism modulo p^N has unit coefficients modulo p^N; lift these units, gauge one system, and apply the construction. It does NOT assert that every truncated system lifts, that an arbitrary outer action lifts, or that there are finitely many truncated classes over an infinite residue field.

For example the source's principal-unit family R=O, Q=C_p, u^p=b is consistent with the result. Deep ratios b'/b have p-th roots once the logarithm can be divided by p. The quotient of shallow units by p-th powers can still be infinite when the residue field is algebraically closed. Finite precision is not finite cardinality.

### 2.4 Uniform denominator from symmetric-order rank and defect

The denominator h need not be left as an unspecified maximum over representatives. Here is a direct bound using the actual primary colength estimate. Suppose R is symmetric of O-rank n≥1 and symmetric-order defect at most d≥0 in the normalization v_p(p)=1 of EEL Definition 3.6. Let

    ν = min{j≥0 : p^j≥n},
    L = ceil(d n/2),
    H = ceil(d)+ν+L.

Choose an integral symmetrizing trace t and dual O-bases (b_i),(b_i^∨). The Casimir tensor C=Σ b_i⊗b_i^∨ lies in R⊗R^op, centralizes R in the separability sense, and z=Σ b_i b_i^∨ lies in Z(R). Over a finite splitting extension, t on a matrix component M_(n_j) is u_j Tr, so

    z_j = n_j/u_j,      v_p(z_j) ≤ v_p(n_j)+d ≤ ν+d.

Each n_j≤n because the sum of their squares is n after splitting. In characteristic zero z is invertible. Thus p^(ceil(d)+ν) z^(-1) is integral in each center field. It belongs to the center of a maximal order Γ containing R: the full integral closure of O in the generic center is contained in every maximal order.

EEL Proposition 3.8 gives ℓ_O(Γ/R)≤e d n/2, where e=v_π(p). An O-module of length l is annihilated by π^l, so p^LΓ⊂R since eL≥ℓ_O(Γ/R). Consequently p^H z^(-1)∈R. The tensor

    e_R = (z^(-1)⊗1) C

has multiplication 1, centralizes R, and satisfies p^H e_R∈R⊗R^op. It is the required separability element with an explicit bound independent of e. No bounded field-splitting ramification has been assumed. Passing to a splitting field above was a computation of eigenvalues, not a replacement of the coefficient ring in the conclusion.

Therefore the thresholds in Sections 2 and 3 can use H instead of h, depending only on p,n,d,|Q|. For a block basic order, EEL Remark 3.7 identifies d with log_p of the defect order and n with the sum of its Cartan entries. The source supplies the boundedness of those data. This closes the potential local uniformity objection without using finite-list maxima. It is still the direct Casimir/colength/separability-lifting construction, and it does not solve global realization or certify an exact block representative list.

## 3. Adding a change of the marked identity component

Eisele's published Lemma 3.4 is stronger than a mere abstract existence assertion: an automorphism modulo π^(2s+1) lifts to an exact automorphism agreeing modulo π^(s+1), provided π^s annihilates all positive Hochschild cohomology. Its proof corrects the product error π^(2s+i)g by a cochain h with δh=π^s g, improving one order at a time. Lemma 3.3 uses Maranda to detect equality of outer automorphisms, and Theorem 3.5 combines both statements.

The same product-error proof works with p in place of π. A separability element with denominator p^h supplies the needed annihilation by the usual separability contracting homotopy multiplied by p^h. In the proof, invertibility modulo p implies invertibility modulo π, so the use of a nonuniformizer does not cause a problem. Explicitly, an O-linear invertible approximation β_i with product error in p^(2s+i)R is changed by p^(s+i)β_i H_i. The cocycle equation for the normalized error and p^s-annihilation supply H_i, the quadratic error has depth 2s+2i≥2s+i+1, and the corrections converge.

Take s=h+a+c−1≥h and T=2s+1. A weak graded O-algebra isomorphism between two crossed products modulo p^T restricts to an automorphism of R/p^T R. Lift this restriction to τ∈Aut_O(R) agreeing modulo p^(s+1), by that proof. After transporting one factor system by τ and lifting the homogeneous unit coefficients of the truncated isomorphism, the two systems agree modulo p^(s+1). Section 2 applies because s+1=h+a+c. Thus a weak labelled graded isomorphism at depth

    T = 2h+2a+2c−1

lifts to a weak labelled graded isomorphism of the exact crossed products. It need not preserve the originally prescribed truncated map at all T digits; the guaranteed initial agreement loses the explicitly stated depths. The construction preserves the base marking only when the initial restriction is the identity; that stronger case was proved directly in Section 2.

This is a composition of the actual primary lifting proof, elementary separability averaging, and elementary finite-group cohomology averaging. It works for arbitrary separable orders and finite Q. It supplies a concrete relative lifting operation, but does not by itself give the distinct substantial full-scope Donovan discovery requested. No new-to-literature or contribution grade is assigned to it.

## 4. Finite integral candidate generation after Frobenius descent

EEL Proposition 3.2 solves the matrix Lang equation by residue Lang followed by successive additive Frobenius corrections. Theorem 3.3 uses a semilinear fixed basis to descend an order invariant under a power of Witt Frobenius to the finite-residue DVR O0=W(F_(p^m)). Theorem 3.9 then does more than state abstract finiteness: after bounding rank n and symmetric-order defect d, it bounds the colength in a maximal order by floor(d n/2) in the unramified normalization. Its proof selects finitely many separable generic algebras and maximal orders, and enumerates sublattices of bounded colength over a finite residue ring. Theorem 3.10 applies this to block basic orders using Cartan and Morita-Frobenius bounds.

For a supplied descended order Λ0⊂Γ with ℓ(Γ/Λ0)≤L, the elementary-divisor theorem gives p^LΓ⊂Λ0⊂Γ. Hence the possible lattices are inverse images of submodules of Γ/p^LΓ. In a chosen basis, closure under multiplication and containment of 1 are finite checks. Symmetry, separable generic type and the required bilinear form/defect constraints must still be imposed; dropping them gives a finite OVERLIST, which is harmless for this coverage calculation but is not a list of realized blocks. If several descent exponents m occur in a known bounded range, a common multiple allows passage to one finite residue field. Isomorphism/Morita comparison of candidates can use basic orders, finite-precision order comparisons, and the relative labelled correction above when extension data are retained.

The operational input is crucial. In the present task the source provides the boundedness/finiteness constructions, but this calculation has not extracted a certified algorithm producing all necessary numeric descent, Picard, geometry and extension bounds from (p,defect order) alone. Even if these bounds are supplied, enumerating the finite overlist is not equivalent to certifying which candidates actually occur as group blocks. Enumeration of finite groups gives positive witnesses when a candidate is realized; it gives no certificate that an as-yet-unseen candidate never occurs. Finiteness of the answer alone gives no detectable stopping event. This is a statement about the constructed procedure, not an impossibility or undecidability claim.

## 5. Where the representation-theoretic reduction stops this attempted construction

A possible way to close a certified representative algorithm would be a bounded-order realization theorem, or an exact finite recognition criterion for the candidate orders with all extension labels. Neither is constructed here. The actual D cone maps cannot supply it by declaration: for cohook moves their controlled errors are nonzero, and their endpoints can have unbounded cuspidal triangle parameters at bounded weight. They bound Cartan data by projective character geometry. They do not identify the block categories with bounded-order endpoint categories.

Conversely, the exact integral Morita transports in ID do handle their intended extensions: the actual n(s,t), central character, dual-recovery corner, Sylow realization, grading, and kernel-removal steps cannot be discarded and then renamed an unpaid gap. Sections 2–3 show explicitly that deep local action/factor errors can also be removed. The remaining need is global effective coverage and exact recognition/realization, not a failure of local integral cocycle correction.

The original i104 history already separates Morita–Frobenius periodicity from arithmetic descent between prescribed endpoints and separates geometric finiteness from certified enumeration. Its finite-field forms with different Frobenius cycles are general symmetric algebras, not block counterexamples. They are not used here to disprove block descent or effectiveness. No blockwise-Alperin endpoint is reopened. The completed r137 P=W scope and all supplied frozen dispositions remain untouched.

The late primitive-alias search also located r67 associativity-correction.md §1. Its actual Casimir/Hochschild homotopy calculation was read after the first draft of these notes, before any freeze. It already uses the contracting-homotopy primitive, in a nonassociative real metric/norm problem. That operation is credited; its norm estimate is not an integral-order denominator estimate. The present local calculation is not nominated on the basis of a new name for that primitive.

## 6. Decision before any theorem freeze

The concrete finite-precision route closes its local operation, including nontrivial actions, all factor equations, p=2, ramification and flat base change. The Casimir/colength calculation also removes dependence on an unspecified separability denominator, replacing it by the explicit H(p,n,d) above. The strongest compatible source/primary mechanisms already pay the surrounding finiteness and lifting ingredients. Turning this into the requested distinct full-scope effective Donovan result would still require the global bounds/recognition bridge described above. No exact full statement with that bridge proved has emerged. Freezing a weaker finite-precision corollary as the requested discovery would not meet the task. Status remains PREFREEZE/no nominee; the calculations are retained for the parent, without mathematical self-gates or count.

## Exact dependency locations

D: field/sections/00_introduction.tex thm:donovan; 02_geometry.tex thm:geometric-cartan; 03_families.tex thm:quasisimple-cartan; complete 04–06 rational-label/runner/cuspidal constructions; 07_extensions.tex def:ext:comparison-data, lem:ext:integral-bases, lem:ext:based-sylow, lem:ext:kernel-removal, thm:extension-finiteness; 08_periodicity.tex prop:sylow-comparison and lem:coefficient-extension. ID: 03_rigidity.tex lem:orbit, lem:HH, thm:gradings, prop:marked; 04_comparison.tex prop:comparison and eq:comparison-exact; 05_sylow.tex lem:induced, prop:sylow-block, thm:based-sylow; 06_kernel.tex lem:restriction and thm:kernel; 07_assembly.tex complete proof and eq:complete-dvr-block-base-change. Full pinned paths, hashes and read extents are private.

Primary operative proof references: [EEL v3](https://arxiv.org/abs/1809.08152), §3, especially Proposition3.8 and Theorems3.3,3.9,3.10; [Farrell–Kessar v3](https://arxiv.org/abs/1805.02015), §§2–4 and8; [Eisele geometry v3](https://arxiv.org/abs/1908.00129), §§3–5; [Eisele published Picard paper](https://doi.org/10.1007/s10468-020-09957-x), Lemmas3.3–3.4, Theorem3.5 and §4. These are actual proof-body reads, subject to the precise version and extent limits in private/READING.md.
