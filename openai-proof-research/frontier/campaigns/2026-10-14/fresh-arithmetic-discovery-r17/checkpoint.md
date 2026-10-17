# Arithmetic discovery r17: Kähler semialgebraic-cover screen

Status: **NO NOMINATION — normal Kähler target remains unpaid.** This is an author's exploratory screen, not an independent proof/contribution verdict. No acceptance, formalization, manuscript, commit, or upload is claimed. The campaign count is unchanged. Work is confined to this fresh r17 directory.

## Scope and chronology

The governing r16 brief was applied to r17 as instructed by the parent. The immutable source pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; source theorems and lower operations are stipulated, not audited. The complete preprint tree supplied all fetched blob identities. The r5–r16 checkpoints were read, with truncated checkpoint displays repaired. OA057, O234, AB194, O217 and root's122 route are not reopened.

Family058 was selected after source-specific history checks. Its faithful full extension would say:

> For every connected normal compact Kähler complex space X, its ordinary universal cover U is biholomorphic to a semialgebraic open subset of a projective variety if and only if U is biholomorphic to D × C^m × F, where m≥0, D is a bounded symmetric domain (a point allowed), and F is a simply connected normal projective variety (a point allowed).

This is a research direction, **not a frozen or proved candidate**. The early parent update said “compact-Kähler extension” without fixing whether singular spaces were included. This checkpoint makes that ambiguity explicit: the full faithful extension retains normal singularities. No assertion is made that an already frozen smooth target was enlarged. The smooth-manifold argument below is technical support and is not substituted for the full normal target.

The initial apparent obstacle was the quotient's missing integral polarization. A real-Kähler graph-degree argument resolves the corresponding compact-factor step once the proper affine-base map exists. Actual primary reading then showed that real-Kähler graph-volume control is already an explicit operation of Claudon–Höring. Their Albanese theorem, however, assumes a manifold; Kollár–Pardon's normal-source bundle theorem assumes projectivity. A resolution is not an automatic replacement for either hypothesis. The full normal case has therefore not been declared solved.

## Actual source contracts

Family058, `Semialgebraic-universal-covers-of-normal-projective-varieties-September-24-2026`, `build/main.tex`, Theorem `thm:main`, has precisely connected **normal projective** X and the displayed product conclusion. Its main wrapper already includes Remmert reduction and Singer vanishing, and its `quasiprojective.tex` already includes quasi-projective covers and projective affine-space uniformization. None is new here.

The complete `quotient.tex`, `groups.tex`, and `compact.tex` were read. The important operation distinction is between projectivity of the ambient presentation and projectivity of the compact quotient:

* `win:construction` only assumes a connected smooth projective ambient Y and a locally pseudoconvex connected semialgebraic open V⊂Y. It has no projectivity premise on a quotient. Its exact full statement and the full `win:tower-properties` proof were read. The intervening inductive window proof is a stipulated lower input and was not fully read.
* The guard, incidence, whole-leaf, exhaustion and inverse-chart construction in `quotient.tex` uses these windows and cocompact deck translations. Projectivity of the quotient enters the stated final compact-fiber conclusions; it is not supplied for a Kähler quotient merely because U has a projective ambient presentation.
* `groups.tex` gives transverse discreteness through countable core levels, proper compactification of incidence families and special abelianity, then removes stabilizers and identifies the bounded symmetric factor. Its core and abelianity interfaces are explicitly Kähler. Algebraization of the finite cover of X is a projective-only convenience; finite analytic covers preserve Kählerness.
* `compact.tex` uses a characteristic free-abelian fiber subgroup, relative Albanese torsors, a proper affine-base map, and an invariant **integral** polarization for the compact-factor marking argument. Its normal-source Albanese and fiber-bundle inputs cannot be silently enlarged to all normal Kähler spaces.

The other family058 companion, `Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026`, has a theorem for bounded semialgebraic affine domains with arbitrary proper cocompact actions, allowing finite stabilizers and requiring no projectivity of the quotient. Its full main wrapper/introduction was read. It already covers that purported extension; it does not provide the missing unbounded/compact-fiber classification.

Family057's actual introduction was fetched and its main theorem and compactifiable-cover corollary with full proof were read. The corollary already states:

1. any connected infinite Galois cover of a normal compact Kähler space which is analytically Zariski-open in a normal compact complex space has virtually abelian deck group;
2. a compact Kähler **manifold** whose universal cover has a Kähler compactification has, after finite cover, an Albanese fiber bundle with simply connected compact Kähler fiber.

The second conclusion is not stated for arbitrary normal Kähler spaces. These are paid source operations, not new deductions of r17 or a relabeling of OA057.

## Complete compact-factor support

`real-class-marking.md` proves the following auxiliary statement under explicit hypotheses. If a smooth semialgebraic projective-open U has a proper holomorphic submersion j:U→T with connected fibers, T is a Stein manifold homeomorphic to Euclidean space, and a compatible proper cocompact group action on T preserves a global closed real (1,1)-form on U which is Kähler on each fiber, then all fibers are biholomorphic. They are automatically projective because they are compact analytic submanifolds of the ambient projective variety.

The proof bounds graph degrees using a fixed ample class on one fiber dominated by a multiple of its real Kähler class. The mixed intersection integrals are constant in the proper smooth family. The finite union of bounded-degree Chow parameter spaces therefore contains every class-preserving isomorphism; homotopy marks its real cohomology class on connected components. The source's finite-component marking and invariant-closed-set rigidity then force one class.

This repairs the particular polarization issue. It does **not** produce j, prove an Albanese bundle theorem for singular Kähler spaces, or formalize the source's geometric construction. It is not a nominee. Claudon–Höring §2.B already explicitly controls morphism graphs by fixed Kähler forms and obtains finite components from bounded graph volume. Kollár–Pardon Definition19 and Theorem20 already use graph bounds to make isomorphism loci manageable. The replacement of an exact integral degree by a finite bounded-degree union is a technical use of those operations.

## Smooth case: what can be transported and what it does not settle

`scope-and-transport.md` records the smooth-manifold transport with every extra interface exposed. It uses Ivashkovich's actual Corollary2(a) to start the source windows; the unchanged whole-leaf and transverse-action mechanisms; the already supplied Kähler compactifiable-cover theorem; the classical relative Albanese construction for smooth proper Kähler families; and the real-class compact-factor argument. This leaves no new claimed mechanism in the smooth special case. No independent correctness verdict for that transport is claimed.

The **full normal target remains unresolved in this packet**. The missing comparison is a normal compact-Kähler version of the bundle/Albanese step with the exact connectedness, fundamental-group, all-fiber flatness and normality properties needed by the later compact-factor argument. CH2013 Theorem1.5 has a smooth-manifold hypothesis. KP2012 Theorem20 retains a normal **projective** source. Resolving N→A changes its point fibers and may change the fundamental group; a product description upstairs does not automatically descend through its exceptional sets. No general descent theorem doing that work was proved or checked here.

It may be possible to extend the primary cycle-space proof. That possibility is not a theorem, a counterexample, or evidence of substantial novelty. Conversely, the present gap is not a proof that the normal extension is false or open in the literature. The normal compact-Kähler Albanese theorem's full primary dependency tree was not exhaustively searched.

## Other prescreens and exclusions

Before058, the catalogue led to042,203,209,210. Actual I104's four-screen introduction shows developed modular/Galois, Broué and tensor work; I102/I98 are the developed K3/Oka lane. Canonical campaign records show209's frozen G4 and recovery, and the older iterations show the developed Foulkes chain. These were not reopened. The searches were source-specific historical exclusion checks, not positive novelty clearance for058. The complete catalogue's372 family titles were read; reading titles is not reading manuscripts. Large combined ledger displays were truncated and are not claimed as full semantic history reads. Relevant actual checkpoints and dispositions were read separately; precise limits are in `reading.md`.

## Formal and integrity boundary

An honest Lean support interface could formalize finite-component marking logic, graph-degree monotonicity under a supplied multilinear positive intersection pairing, and the finite-index characteristic-subgroup construction. It would leave compact complex geometry, Chow spaces, the source window theorem, Kähler Hodge theory and the disputed normal Albanese bridge as explicit external assumptions. No Lean file was written, and formalizing such support would not solve the full target.

Receipts bind22 pinned source bodies and5 primary PDFs plus their extracted texts. Downloaded bodies are not thereby read. `verify.py` checks exact file membership, hashes, source Git blob identities and primary receipts against externally supplied manifest/checkpoint anchors; deliberately incorrect anchors must fail. Integrity is not mathematical proof or contribution assessment.

Final author disposition: **NO_NOMINATION**. A technically paid real-class repair and a smooth transport have been retained; the faithful normal Kähler target is not proved, narrowed, or counted.
