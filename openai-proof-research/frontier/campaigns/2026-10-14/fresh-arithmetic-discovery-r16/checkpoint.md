# Arithmetic discovery r16: complete technical screen and a separate obstruction

Status: **NO NOMINATION**. This is a discovery checkpoint, not an independent proof/contribution verdict. No new accepted result, publication, shared-ledger change, or formal-completion claim is made. The campaign target remains twenty; this packet does not change its count. All files belong to the assigned r16 directory.

## 1. Contract, chronology, and fixed target

The r16 brief requires a substantial full-scope deduction from the pinned source truths at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with actual primary-operation comparison. Prior developed-chain exclusions remain in force. In particular this work does not repackage OA057, O234, AB194, the r15 King extension, the r15 curvature-twisting extension, the reserved O217 universality result, or root's family122 route. No nested agents were used.

The first selected pre-freeze target, reported to the parent before its primary comparison was finished, was:

> For every smooth connected projective complex surface S with p_g(S)=q(S)=0 and torsion-free integral cohomology, for every n>=0, the integral Chow motive of S^[n] is a finite sum of Tate motives. Consequently, for every i, CH^i(S^[n]) -> H^(2i)(S^[n],Z) is an isomorphism, and all odd integral cohomology vanishes.

The quantifiers were not reduced to Hilbert squares, particular surfaces, rational coefficients, or bounded n. The target is true under the stipulated source, but its full mechanism is paid by primary results below. It was never frozen as a substantial candidate. The initial suspected unpaid operation was removing the denominators in the rational Hilbert-scheme motive decomposition. Totaro's 2020 paper supplies exactly that operation by a different, already published construction.

After that rejection, a separate family052 screen tested whether the source's two integrable complementary summands could be replaced by arbitrarily many individually integrable summands. This fails by an explicit classical example. The two screens therefore have distinct outcomes: a complete technical transfer and a false proposed strengthening.

## 2. Pinned family040 source contract

Manuscript: `preprints/Blochs-Conjecture-for-Surfaces-with-pg-equals-q-equals-0-September-24-2026/`.

The introduction's Theorem `thm:bloch` asserts the integral degree isomorphism CH_0(S)=Z for p_g=q=0. Corollary `cor:tate-motives` already gives

    h(S)_Q = 1 + L^(direct sum b_2(S)) + L^2,

pure Tate rational motives for every power and every S^[n], rational cycle-class isomorphisms, and vanishing odd rational cohomology. The complete conclusion section explicitly derives the Hilbert-scheme claim from de Cataldo--Migliorini, including the quotient averaging projectors 1/|Sigma_nu| sum Gamma_sigma. Thus rational Hilbert-scheme Tate statements cannot be nominated as new here.

Those source statements are adopted as true. The upstream virtual Quot proof is not audited. The rational motive statement also supplies the exact generic-field hypothesis required by Kahn: CH_0(S_C(S)) tensor Q = Q. No inference from integral CH_0(S)=Z alone is silently substituted for this hypothesis.

## 3. Complete operation-by-operation proof of the integral target

### 3.1 Integral surface input: Kahn's torsion order

Bruno Kahn, *Torsion order of smooth projective surfaces* (2016), Definition 1.5 and Lemma 1.6 define Tor(S) as the order of the generic point modulo cycles from S, or equivalently the order of the normalized birational motive. Lemma 1.6 states that Tor(S) annihilates CH_0(S_F)^0 for every extension F/C.

Assumption 5.2 is: algebraically closed ground field, X a surface, and CH_0(X_k(X)) tensor Q = Q (with a projective auxiliary Y in that section). Corollary 5.4(b) gives

    Tor(S) = exponent(NS(S)_tors)

in characteristic zero. Its convention gives exponent one for the zero group. This is an equality, not merely a lower bound from cohomology.

For our S, the exponential sequence and p_g=q=0 identify Pic(S)=NS(S) with H^2(S,Z). The latter is torsion-free by the target hypothesis. Hence Tor(S)=1. A complex point of S remains a degree-one point over every extension F/C. Lemma 1.6 therefore yields CH_0(S_F)=Z by degree for every such F.

### 3.2 From universal Chow groups to an integral Tate surface motive

For every extension F/C, the base-change maps in all Chow degrees of the surface are surjective:

* CH^0(S)=Z is unchanged since S is geometrically integral.
* CH^2(S_F)=CH_0(S_F)=Z by the preceding paragraph.
* CH^1(S_F)=Pic(S_F) is obtained from Pic(S). Here Pic^0(S)=0, so the Picard scheme is a constant discrete group over the algebraically closed field C. Equivalently, geometric line-bundle classes are the same Neron--Severi classes after extension. The potential Brauer descent obstruction vanishes for these classes because S_F has an F-point: Br(F) -> Br(S_F) is injective. Every resulting class is already represented by a line bundle on S.

Burt Totaro, *The motive of a classifying space*, Geometry & Topology 20 (2016), Theorem 4.1, says precisely that universal surjectivity CH_*(M) -> CH_*(M_F) for finitely generated F/k makes M a direct summand of a finite Tate sum. Over a PID, including Z, it is a finite Tate sum itself.

The proof is operationally relevant: localization and induction on the dimension of an arbitrary auxiliary scheme turn fieldwise surjectivity into the Chow Kunneth surjectivity. Applying this to the dual motive expresses the identity/diagonal as a finite sum of external products. The associated maps split M off a Tate sum. Projective modules over Z are free. Thus h(S)_Z is integrally Tate. This is not a new cancellation or nilpotence lemma.

### 3.3 All n: Totaro's exact integral Hilbert-scheme operation

Burt Totaro, *The integral cohomology of the Hilbert scheme of points on a surface*, Forum of Mathematics, Sigma 8 (2020), e40, Theorem 4.1, states:

> For a smooth projective surface over a field and a characteristic-zero PID R, if its Chow motive with R coefficients is a finite direct sum of Tate motives, the same is true of the Hilbert scheme of n points for every n>=0.

Apply this with R=Z and the surface input above. The statement already has the entire required n range and integral coefficients.

Its proof pays the initially suspected denominator obstruction. The Gholampour--Thomas nested-Hilbert obstruction formula gives the diagonal class as an integral top Chern class of the derived Hom complex of the two universal ideals. Integral Tate input gives the required algebraic K-theory Kunneth decomposition. Expanding the universal ideals, then pushing the derived Hom expression by the Mukai/Euler pairing, expresses this Chern class as an integral sum of external products. Splitting the diagonal gives a Tate summand, and the PID condition makes it a Tate sum. No division by partition stabilizer orders is introduced.

Each integral Tate summand has one integral cycle generator in its even realization degree and zero odd realization. Correspondences preserve cycle class. This gives all asserted integral cycle-class isomorphisms and odd vanishing. The case n=0 is a point.

Totaro's Theorem 3.1 separately proves torsion-free cohomology of all S^[n] from torsion-free cohomology of S; that theorem alone would not prove the integral Chow assertion. The proof above uses Theorem 4.1 with its stronger motive input.

## 4. Contribution decision and the genuine remaining torsion issue

The full chosen theorem is a new instantiation of published operations after the stipulated Bloch result. It adds no new integral diagonal, K-theoretic, or all-n argument. **Classification: TECHNICAL; do not nominate.** This conclusion is based on exact primary mechanisms, not absence or presence of a matching title.

The torsion-free condition was part of the initial target. Removing it is a different problem and is not claimed here. For example, the route through Kahn produces Tor(S)>1 when NS(S) has nontrivial torsion, so universal integral CH_0-triviality and integral Tate motives no longer follow. Merely renaming this obstruction as a new problem gives no proof.

Inverting N=exponent(NS(S)_tors) would again be a paid extension: Kahn's annihilation statement gives universal CH_0-triviality over Z[1/N], the same Picard argument gives universal Chow surjectivity, and both Totaro results apply over this PID. That observation is not a replacement target or a nomination. No assertion is made here about the full integral Chow motive or torsion order of arbitrary S^[n] when N>1.

## 5. Independent family052 screen: individual integrability is insufficient

The pinned `Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/build/intro.tex` assumes two integrable complementary holomorphic subbundles. Its discussion of Beauville's multiple-summand conjecture explicitly requires integrability of the relevant partial sums. It also already describes the classical counterexample below. A compatible product must respect the prescribed summands; an abstract product decomposition of the underlying manifold is not enough.

Let A=E x E be an abelian surface with independent translation vector fields u_1,u_2. On P^1 take, on the affine coordinate chart z,

    v = d/dz,       w = z d/dz.

These are global holomorphic vector fields: in the other chart zeta=1/z they are -zeta^2 d/dzeta and -zeta d/dzeta. Their bracket is [v,w]=v, which is not identically zero. Put X=A x P^1 and

    E_1 = O_X (u_1+v),
    E_2 = O_X (u_2+w),
    E_3 = p_(P^1)^* T(P^1).

Projection to T(A) proves the first two fields are everywhere nonzero and independent, and that E_1+E_2 intersects E_3 trivially. Thus T(X)=E_1 direct-sum E_2 direct-sum E_3. Each E_i has rank one, so each is integrable.

But [u_1+v,u_2+w]=v is a nonzero vertical field and is not in E_1+E_2 wherever it is nonzero. That rank-two partial sum is not integrable. A compatible three-factor product on the universal cover would make every partial sum tangent to a product of factors and hence integrable. Integrability is local and descends through a covering local biholomorphism. This is impossible.

Andreas Horing, *Uniruled varieties with split tangent bundle*, arXiv:math/0505327, Example 2.14 in the downloaded version, attributes precisely this construction to Beauville. The displayed three-line version simply refines its rank-two bundle into the two explicit global lines already in that example. This is a known obstruction, not a new counterexample. **Classification: FALSE strengthening, already classically obstructed.** No smaller positive theorem is nominated.

## 6. Formal feasibility and adversarial checks

For the integral route, an honest feasible Lean fragment could formalize splitting an identity by mutually composable maps or the PID/module algebra after explicit motivic input interfaces. It would not formalize the surface geometry, universal Chow descent, universal-ideal derived K-theory, or the integral diagonal formula. Those are exactly the published paid operations. No Lean file was commissioned merely to formalize a technical transfer; no full formal theorem is asserted.

For the obstruction, a polynomial derivation calculation can check [d/dz,z d/dz]=d/dz. The global vector-bundle and covering conclusions still require their stated geometry. An implementation of that bracket would not turn the classical example into a contribution. No numerical experiment is needed for either exact argument.

Checks against tempting overclaims: integral CH_0 over C is not silently treated as universal integral CH_0; the rational motive supplies Kahn's actual assumption. Odd rational vanishing plus torsion-freeness is not silently used to conclude integral Chow surjectivity; Totaro's motive theorem is used. The source's rational Hilbert decomposition is not relabelled integral. The tangent counterexample concerns a specified splitting, not the existence of some product structure. Rank-one integrability is not confused with partial-sum integrability.

## 7. Provenance and honest reading limits

`receipts.json` records exact pinned paths, URLs, Git blob SHA-1 and SHA-256 for 17 source bodies. All listed bodies were retrieved and authenticated against the complete pinned preprint tree. Retrieval is not a claim of reading.

Actual source reads: family040 introduction and conclusion completely, including the full rational Hilbert motive proof; family052 universal-cover introduction and its main wrapper completely. The other family040 proof sections and the rationally-connected family052 companion bodies were fetched for inventory/context but not read or used as proof inputs in this screen. Earlier inherited r5-r15 screen dispositions were retained; no claim is made of rereading every historical source during r16. A large catalogue reread during continuation was truncated; it was not treated as a new complete catalogue read. The complete-tree inventory and earlier catalogue/history screening remain context, not evidence of an individual theorem.

Actual primary reads, with line numbers referring to retained pdftotext output:

* `totaro2020.txt`: complete six-page paper, including its theorem statements, proofs, and references.
* `totaro2016.txt`: lines 510-650, containing complete Theorem 4.1, the relevant motive definitions, and its proof; not the whole classifying-space paper.
* `kahn.txt`: introduction/abstract excerpts; lines 85-180 (definitions, birational-motive convention, torsion order and Lemma 1.6); 465-487 (Assumption 5.2 and context); 535-650 (proof of Theorem 5.3, Corollaries 5.4/5.5, relevant remarks). Other sections and appendix not fully read. The quoted corollary is relied on as a primary theorem; its entire dependency tree was not independently re-proved.
* `hoering.txt`: lines 200-240, including the integrability argument and complete Example 2.14. Not the full paper.
* `totaro.txt` (Hilbert square paper): introduction/search snippets only. It was not used to establish any result in this checkpoint. In particular no claim about its torsion examples is needed here.

Primary URLs and both PDF/text body hashes are in `primary-receipts.json`. These are author-hosted PDFs or arXiv, not secondary summaries. No blanket claim about current open status follows from the open-question paragraph of a 2020 paper.

`manifest.json` inventories every packet file except itself. `verify.py` requires caller-supplied external manifest and checkpoint SHA-256 anchors, checks exact inventory, verifies all file hashes, and replays pinned-source Git blob comparisons. Positive and deliberately wrong-anchor controls are reported to the parent separately after sealing. Integrity checks establish file identity, not mathematical proof or substantial contribution.

Final disposition: two distinct screens completed, no new substantial full-scope theorem nominated. The full integral target is technically proved by the exact published chain above; the many-summand strengthening is false for the explicit classical reason above.
