# I246 — contribution analysis

**Verdict: SUBSTANTIAL, for E4's contribution gate only.** This is a judgment of mathematical increment relative to the inspected primary results, conditional on the separate proof gate accepting the exact I242 argument. It is not a proof-gate conclusion, an assertion of worldwide priority, or authorization to change the accepted count.

The reviewed proof is `frontier/experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md`, SHA-256 `03c0f05cef564e1bde2630ed725ff755d3bb603ea07dbd39a711e595e96d6627`. The supplied final iteration summary is a different file, SHA-256 `2bba0807883573e6b4287dbb6b1daac0e9cd9169f87ceb6b463d2e36ec12b2e6`.

## Exact object assessed

For each integer 1≤n≤4, A∈M_n(C), finite m≥1, and finite-degree P∈M_m(C)[z], put M=max_{W(A)}||P(z)||. If M>0 and ||P[A]||=2M, E4 asserts that W(A) is a positive-radius closed disk and that **the same P** has unit coefficient vectors u,v with

p(z)=v*P(z)u,   ||p(A)||=2M,   max_{W(A)}|p|=M.

This is attained polynomial equality. The hypothesis does not merely say ψ_cb(A)=2. The conclusion does not classify the entire amplified operator P[A] as a reducing nilpotent block. Nor does it provide a rate for near-equality, constants depending only on an inball radius, or an extension to arbitrary base dimension. The scalar monomial conclusion after disk normalization is credited to existing scalar interpolation/equality theory.

## Primary-source comparison

The exact primary statements and selected proofs were read, including **all of ACV v3 Sections 5, 7 and 11**, and Jin v2 Sections 1–8. References and retained texts are in [literature.md](../../sources/i246_crouzeix_rigidity_contribution/literature.md).

ACV's Theorem 5.3 supplies a minimal rectangular extremal with mutually orthogonal base Schmidt families and r+s≤d. Its Section 7 proves the complete bound and scalar/complete equality equivalence for d≤3 by eliminating the remaining row/column cases. In dimension four its reduction leaves a (2,2) level. Section 11 combines that d≤3 equivalence with scalar rigidity; Theorem 11.2 is scalar polynomial classification in all finite dimensions, while Corollaries 11.4–11.5 are the complete conclusions only through dimension three. The later Section 11 inverse-algebra results remain scalar and impose their own hypotheses. [ACV v3](https://arxiv.org/html/2608.27346v3).

Jin's Theorem 1 concerns ψ(A), defined using scalar polynomials. It includes scalar suprema that need not be attained by polynomials; Lemma 4 supplies finite scalar Schur interpolation, and Corollary 1 concerns scalar holomorphic equality with interior spectrum. None converts an arbitrary matrix polynomial into a scalar compression. [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2).

The stipulated direct manuscript supplies the original-matrix positive field, both multiplication orders, and the positive-block trace comparison; its companion supplies a common positive density after similarity and equality fibers. Their actual theorem statements do not state E4. The input identities and the I238 deficit bookkeeping receive no novelty credit here. The pinned raw bytes and Git blobs were independently authenticated, without auditing their truth.

## Why the old transfer does not already supply the increment

There are three logically different assertions:

1. A scalar extremizer exists for a base matrix.
2. A complete extremizer exists at some finite rectangular level.
3. For the specified complete polynomial extremizer P, one can choose constant coefficient vectors u,v so that v*P u is extremal.

The third is E4's operative new assertion. A scalar theorem applied after assertion 3 gives disk geometry, but cannot establish assertion 3. General finite-level compression retains Schmidt ranks as large as the base dimension. Orthogonality alone permits two mutually orthogonal two-dimensional supports in C^4. Even ruling out a minimal rectangular extremal by an old row/column argument would need a separate argument for compression of the original P.

Replacing A by I_m⊗A does not turn P[A]=Σ A^k⊗P_k into a scalar polynomial of that amplified base matrix: scalar polynomials there have scalar coefficient factors. The absence of a scalar transfer is structural, not a notation issue. A common positive dilation also allows matrix-valued isometric channels, so equality of its operator norms cannot simply be read as a scalar maximum principle.

I238's exact A=[[0,2],[0,0]], P(z)=[[0,z],[1,0]] obstruction is decisive against one tempting shortcut. P[A] has weights (1,2,1), norm 2 and top-vector second iterate of norm 2. Its scalar square-function sum at that vector is 9/4. Thus importing scalar output nilpotent rigidity would be invalid. E4's conclusion remains consistent: the (1,2) scalar compression is p(z)=z. The new assertion concerns input coefficient factors, not the output block structure.

## The contribution-bearing step

In the candidate, the controlled exterior limit converts the inherited integrated equality into

X*Y=0,   H(t)^(1/2)(XX*−YY*)H(t)^(1/2)=0 a.e.,

for the **original** positive boundary field. Let p=rank X and q=rank Y. The second relation makes ran H totally isotropic for a form with inertia (p,q,d−p−q). On a simple-support arc, rank H=d−1, whereas a totally isotropic subspace has dimension at most d−max(p,q). The conjunction forces p=q=1.

The trace identity, inertia formula, Herglotz representation, Fourier-tail estimate, support-eigenvalue differentiation and anticommuting-generator calculation are individually standard or supplied. Their conjunction connects two previously distinct pieces of information: complete functional-calculus equality and the codimension-one geometric kernel of a supporting half-plane. This identifies the coefficient channel itself. That is an inverse theorem for the complete certificate, not an additional numerical bound extracted from the same inequality.

The boundary limit matters to that increment: the inherited certificate lives on strictly enclosing analytic domains, where γ_j need not equal 2. The candidate keeps the normalization, bounds its coefficient energy using strong L² convergence, and then passes the quadratic trace slack. Merely setting γ=2 in a collar, or passing a quadratic expression through weak convergence, would not justify using the boundary rank. The limit is supporting technical work; no independent substantiality award is assigned to compactness itself.

The small-dimensional anticommuting calculation ensures the needed simple support arc for each irreducible block of size ≤4. It earns no separate credit as new algebra. Its role is to remove a hypothesis from the geometric-to-coefficient implication in the first dimension with two-sided non-scalar Schmidt supports.

## Scope and the unchanged standard

The increment from base dimension three to four is not credited merely because 4>3. It is credited because the surviving two-sided coefficient case requires additional geometric information that the old dimension count and row/column square functions do not supply. The inverse mechanism also states a usable conditional scalarization principle at a simple-support arc, although no higher-dimensional theorem is nominated here.

Arbitrary finite coefficient size is genuine quantified scope, but finite compression was already known; its unbounded notation alone is not an independent discovery. The substantive reduction is all the way to one coefficient input and one coefficient output for the specified witness. Arbitrary finite degree likewise removes an artificial quadratic restriction, but contributes less weight than that rank reduction. The source estimate already permits every degree, and once the geometric rank argument applies, no degree-two algebra is needed. Reducing a polynomial modulo the minimal polynomial preserves P[A], not its boundary supremum, so the all-degree assertion is not obtained just by truncation. Conversely, high-degree entries in unused channels can be harmless, so this scope should not be advertised as an independent new high-degree extremizer theory.

On the operational standard in the task—new structural content rather than bookkeeping, parameter substitution, or generic compactness—E4 clears the contribution threshold. It resolves the exact-equality first target in the first unhandled complete coefficient configuration and supplies a witness-level conclusion. I do not infer the threshold from the count nine, or inspect unrelated accepted findings to manufacture a comparison.

## Novelty limits and disposition

The bounded searches and the actual primary passages provide positive evidence of a gap and of a mechanism addressing it. They do not establish exhaustive priority. No primary statement inspected already contains the asserted dimension-four complete scalarization. Search misses alone are not the reason for the verdict.

The classification is **SUBSTANTIAL**, not KNOWN or merely TECHNICAL, for this combination and exact scope. It is not UNRESOLVED merely because a worldwide novelty search is impossible: the supported contribution assessment can be made with an explicit literature boundary. Proof correctness, independent external theorem validation beyond scope reading, and integration into the ten-finding count remain outside this gate. The positive-deficit quarter-power problem and nonattained ψ_cb equality are explicitly not paid by this verdict.
