# Arithmetic r14: two developed screens and two history exclusions

Status: NO_NOMINATION. Target20/accepted10 unchanged. No immutable campaign candidate was frozen, no theorem was weakened after selection, and no favorable proof or contribution verdict is requested. This report retains one fully developed geometric transfer and one explicit conditional multi-parameter transport construction, together with their contribution/gap boundaries. It does not claim either as a substantial new finding.

## 1. Family004: canonical ampleness does not create a substantial new mechanism

Read complete pinned H10(Q) introduction and consequences. `thm:main` is ordinary rational solvability undecidability with variable count part of input. `thm:degree-normal-form` already supplies quartic and sum-of-quadratic-squares forms and Turing degree0′; its reduction from integer solvability is Turing, not an asserted many-one reduction. None of these is new here. Rational singular-point packaging is already developed in proposals/algebra_geometry.md and is excluded.

Poonen, *Existence of rational points on smooth projective varieties*, JEMS11(2009),529–543, DOI10.4171/JEMS/159, https://math.mit.edu/~poonen/papers/chatelet.pdf: actual primary reads are extracted lines1–155 and400–531. These include the complete main statements, §§8–10 and proof endings. Earlier Châtelet construction internals and §11 were not fully read. Theorem1.3 already constructs effectively, from projective X and open U, a smooth projective Y→X whose rational-point image is U(Q). Section9 handles its apparent ineffective Faltings choice by a computable finite union. Section10 handles geometric integrality via connected components and excludes components with no possible rational point. Thus smooth projective rational-solvability undecidability is a direct primary reduction, not a new deduction mechanism.

### 1.1 Complete additional geometric construction

Let k be an infinite characteristic-zero field and X a smooth projective geometrically integral k-variety of dimension n. Choose N≥max(2,n+1), a k-point p∈P^N and a very ample line bundle L on X such that K_X⊗L is ample. Choose d≥N+2. There is a smooth projective geometrically integral hypersurface

    Y ⊂ X × P^N,
    [Y] = pr_X^*L ⊗ pr_P^*O(d),

containing Z=X×{p}. Projection r:Y→X and inclusion s:X→Y satisfy r∘s=id_X. Moreover K_Y is ample. In particular Y(K) is nonempty iff X(K) is nonempty for EVERY field extension K/k.

Proof. In homogeneous coordinates p=[1:0:…:0], take the linear system of sections of L⊠O(d) vanishing on Z. Its only base locus is Z. It separates first jets off Z (L is very ample and degree-d forms vanishing at p separate first jets away from p for d≥2), so Bertini gives smoothness away from Z for a general section. Along Z, its N normal derivatives are independent arbitrary sections of L, the coefficients of y_0^(d−1)y_i,1≤i≤N. A general N-tuple has no common zero: the incidence of a point x and N sections all vanishing at x has codimension N in the parameter fiber, and dim X=n<N. Thus a general hypersurface is also smooth along Z. Both open conditions are defined over k, and the nonempty open of the parameter vector space has a k-point because k is infinite.

The divisor Y is ample in the smooth geometrically connected projective variety X×P^N, whose dimension is at least2. The connectedness theorem for ample effective divisors makes Y geometrically connected. Smoothness then makes its geometric irreducible components disjoint, so it is geometrically integral. Adjunction gives

    K_Y = ( (K_X⊗L) ⊠ O(d−N−1) )|_Y,

which is ample. Projection and the contained section establish the retraction and the rational-point equivalence. This also explains why merely using a plane fiber would fail in arbitrary base dimension: only two normal derivatives can acquire a common zero when n≥2. The choice N>n pays precisely that local smoothness issue. It introduces no unproved rational-point lifting principle.

Over Q, the construction can be searched effectively using a sufficiently positive supplied embedding, polynomial equations, and smoothness/geometric-integrality checks; positivity can be certified from the displayed adjunction expression after choosing L sufficiently positive. Coupled with Poonen, it gives the expected undecidability transfer to canonically polarized varieties with unbounded dimension. No fixed-dimension undecidability, hyperbolicity, or many-one completeness is asserted.

### 1.2 Operation comparison and disposition

The input undecidability is stipulated source004. Elimination of affine boundaries is Poonen's existing arithmetic operation. The extra operation above is Bertini with a prescribed smooth base locus, choosing its codimension larger than its dimension, followed by adjunction and a section/projection argument. The necessary smoothness check is explicit, but no further mechanism remains unpaid. This is a technical geometric packaging, not a substantial campaign nomination. Search absence for the exact phrase “canonically polarized retract” is not a novelty argument. A full literature novelty claim or formal certification is not made.

## 2. History exclusions checked before developing replacement claims

Family039 weighted maximal Seshadri positivity is ALREADY DEVELOPED in I136. Actual I136 §§4–6 and its final status were read, including the mixed Hermite-jet container M^(n−1)S≤V, the convex equal-subset method, and the diffuse two-level vector lying outside both methods despite Σw_i^n<V and maxw_i→0. Its full weighted-volume target is unpaid and excluded from this fresh lane. No new039 source theorem is claimed from a catalogue summary.

Family059 scalar-block amplification and Hölder comparison are ALREADY DEVELOPED in arithmeticr8. Its checkpoint was re-read at the operative lines, and the complete source introduction and seeds were inspected again. The source already states right equivalence, corank failure, and common-square initial-form Milnor-fiber failure. No product, power, common suspension, or radial Hölder consequence is nominated. The r8 scalar-block isolation obstruction remains unchanged. The combined display of source introduction/conclusion/seeds truncated part of conclusion; this task does not claim a fresh full conclusion read.

## 3. Family064: several-parameter triviality and the precise missing interface

The pinned source theorem concerns a holomorphic family F(x,t), x∈C³, t in a complex DISK, with F(0,t)=0, isolated critical points at0, and constant Milnor number. It supplies a jointly continuous ambient right trivialization and inverse after shrinking. Actual new complete reads: introduction, §12 `prop:resolved-family`, §16 `prop:continuous-gradient-lift` and both corollaries including proof endings. The numerical/surface-comparison chain §§2–11 and the closed-ball/seam construction §13 were fetched but NOT fully read in r14; no new use of their internal claims is made.

The distinct full direction screened is: for every m≥1 and every holomorphic μ-constant family of isolated surface hypersurface singularities over a neighborhood B⊂C^m of0, does the entire family admit a jointly continuous local ambient right trivialization, preserving the base and origin section? This is a pre-freeze research direction, not a completed theorem. A supplied simultaneous resolution is NOT part of this full target.

### 3.1 What disk triviality actually gives

For each sufficiently small parameter t, restrict to the complex line through0 and t. Local disk triviality at every point of a compact segment, followed by a finite chain of local equivalences, identifies the individual germs at0 and t. It does NOT by this argument choose equivalences continuously as the direction t varies. A family of independently chosen line trivializations is insufficient for the full target.

### 3.2 Complete conditional extension of the actual transport operation

Suppose, in addition to the analytic isolated-axis and multi-parameter small-o gradient conditions, that there is ONE proper holomorphic modification b:M→{F=0}, isomorphic away from the origin section A, with M→B smooth and E=b^−1(A) relative normal crossings. Then the source §16 construction works for all2m real coordinate directions:

1. Relative normal-crossing charts lift each coordinate direction tangentially to every branch of E. A smooth partition of unity patches the lifts without changing their projections or tangencies.
2. Push the fields to the punctured zero family. Properness and tangency force their spatial parts to tend to0 near A, exactly as in `cor:gradient-resolution`.
3. No trajectory of any constant real combination can reach A in finite time: lift it to the proper inverse image of a compact terminal arc, extend the smooth ODE there, and use uniqueness plus tangency to E in both time directions.
4. For each coordinate direction a, the ambient gradient lift K_a uses the relevant parameter derivative F_a and satisfies dF(K_a)=0. Correct it by extending the kernel-valued difference from the punctured zero family with the variable-radius tubular retraction and orthogonal projection from the source proof. The correction tends to0 at A.
5. Peano existence, smooth uniqueness off A and the no-endpoint condition give uniqueness everywhere. Boundedness on a common compact neighborhood plus the integral-equation/Arzelà–Ascoli argument gives joint continuity including at A and for reverse flows.
6. Compose the2m coordinate flows in a fixed order for the parameter coordinates. Shrinking once gives a common domain for this finite list. Reverse the order and times for the joint inverse. Commutation or flatness of the fields is unnecessary because the ordered path is fixed.

Thus the entire conditional result is the source's existing transport operation applied to finitely many directions. It is technical. It does not solve the full target by adding the simultaneous-resolution hypothesis silently.

### 3.3 Primary comparison and unresolved point

Okuma, *On (−P·P)-constant deformations of Gorenstein surface singularities*, CMH79(2004),647–658, DOI10.1007/s00014-003-0791-8, https://ems.press/content/serial-article-files/43021, was fetched. Actual read range from web extraction: lines0–223 (through the opening of §3), plus references and selected later displayed passages returned by the tool. This is not a full-paper read. Its Theorem1.2 explicitly assumes a one-dimensional disk base, and its §3 setup uses a weak resolution over the punctured disk. This does not by itself give a simultaneous resolution over arbitrary higher-dimensional bases.

Okuma's introduction recalls Laufer's Theorem6.4 relating topological constancy and weak simultaneous resolution. That original theorem's exact general-base hypotheses were not retrieved here. King1980's publisher PDF URL redirected to a subscription preview; the original proof was not read. King's author bibliography lists the paper but provides no download link. Search snippets and a textbook footnote suggest a classical constancy-to-triviality mechanism, but are NOT treated as an invoked theorem or a novelty verdict.

Accordingly the current full direction is UNPAID / PRIMARY-INTERFACE-UNRESOLVED. The remaining step is either (a) check a classical arbitrary-base theorem which already makes the extension technical, or (b) construct uniform simultaneous resolution/controlled transport and descent over the multi-parameter base with actual proof. Diskwise small-o estimates alone do not do this. There is no claimed counterexample to full multi-parameter triviality.

## 4. Integrity, chronology and formal boundary

All pinned fetched text/source bodies are in receipts.json with exact raw URLs, SHA256 and independently matched Git blob SHA1 from complete preprints-tree.json. Download does not mean read. The source truths are accepted; no upstream consistency argument or internal source audit was attempted. The campaign exclusions OA057/O234/AB194/r5–r11 and r13 remain unchanged.

The actual sequence was004 source and primary reduction → canonical-ampleness construction →039 history exclusion →059 history exclusion →064 source transport and actual Okuma scope comparison. No promising exact target was frozen and later replaced by a weaker one. Both active constructions have precise limitations above. No nested agents, shared-ledger edits, staging, commits or uploads occurred.

Formal feasibility is limited: the retraction's field-point implications and finite composition/inverse algebra can be isolated as supporting lemmas, but would not formalize Bertini, adjunction, topology of singularities, simultaneous resolution, or the full analytic ODE argument. No Lean completion is claimed and no Lean file was written. No independent proof/contribution review should be requested on this packet as a substantial candidate.
