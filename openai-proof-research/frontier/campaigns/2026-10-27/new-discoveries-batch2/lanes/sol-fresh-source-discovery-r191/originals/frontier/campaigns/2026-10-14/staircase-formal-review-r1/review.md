# Independent semantic and kernel audit: PASS

**PASS for the advertised scoped Lean support. No required repairs.** The source proves a meaningful conditional regular-coordinate splitting over arbitrary commutative unital rings, its equivariance, injectivity and invariant complement, and preservation of split/intertwining identities by scalar extension without flatness. Its README and paper correspondence accurately delimit this coverage. This verdict does **not** certify a Lean proof of the staircase theorem, establish the staircase separation hypothesis, repeat the full proof/contribution gates, or pass the manuscript gate.

Myeongjin Kang, no affiliation, 2026-10-15. Original review prose: CC BY 4.0; original review code: MIT. Copied author materials and third-party dependencies retain their notices and rights. Work and disposable compilation directories were confined to `staircase-formal-review-r1/`. No staging, commits, uploads, subagents, acceptance or count action. The user-reported count remains **3/10**.

## Identity, reading, and boundary

The audited original is `../staircase-formal-v1/StaircaseSupport.lean`, 7,945 bytes, SHA-256 `a8a8473d98a673790eb8e72546b890aa93bfba02351a97f401c39d4dbc10e989`. Its output manifest has 17 file records, plus the manifest itself, and SHA-256 `5ff7c5b4e0504d88e1409065129bcef9737160d9484abaa212c7bd69151fd3a0`. Its input manifest has 13 records. I read all 18 delivered author files in full, including the source, controls, exact-type/axiom logs, README, correspondence, rebuilding/verifying scripts, receipts, lock, manifests, and license; the source compilation log is an empty successful log. I ran the original read-only verifier successfully. The complete copied author package in `author-copy/` remains byte-for-byte identical after rebuilding it with the explicit original cache path.

I also read the complete frozen candidate, proof review, contribution review, parent contribution disposition, and current manuscript. The frozen context hashes match the brief:

- Candidate: `6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179`.
- Proof review: `85cdaff75e27300815f81a28fc709a5714b16fa1941d023f44238b302e549e80`.
- Contribution review: `47de7398e889efb726de5e993384ace4e3e1f83d095e37a68a309f5aaa64b060`.

`input-manifest.json` records local input hashes, byte lengths and actual semantic read extents. Authentication is of local bytes, not a fresh remote source authentication. I read `AGENTS.md`, the immutable source pin, and the relevant catalogue item 205. No upstream mathematical theorem is invoked by this Lean source; accepted upstream truth is not re-audited. The prior PASS and narrowly SUBSTANTIAL verdicts are context, not Lean premises or new findings of this review. Bryant–Kovács' separating-product mechanism is classical; no field injectivity result is imported over the integers. Ikenmeyer's uniqueness and the pinned square-deficit operation remain inherited, and complex regular containment/characteristic-2 PIM occurrence remain antecedents. No priority claim is made.

## Exact semantic contract

The full elaborated types and axiom closures of the author's four definitions and sixteen theorems are in `logs/author-types.log`, independently regenerated from freshly copied source. They agree with the author's saved log. The load-bearing splitting interface has precisely

```
{R G M : Type*} [CommRing R] [Group G] [Fintype G]
[AddCommGroup M] [Module R M]
ρ : Representation R G M
z : M
θ : M →ₗ[R] R
sep : ∀ g, θ (ρ g z) = if g = 1 then 1 else 0
```

and concludes

```
(coefficientMap ρ θ).comp (orbitMap ρ z) = LinearMap.id
```

There is no `Nontrivial`, characteristic, field, domain, semisimplicity, finite-dimensionality, freeness or torsion-freeness assumption on the ambient module; no commutativity of the group; and no flatness assumption. Universes are polymorphic. `Fintype G` is the finiteness data needed for the orbit sum. The elaborator omits it from `regular`, `coefficientMap`, `Separates` and the statements which do not need that sum, as the exact log confirms.

`Separates` is an ordinary defined predicate and an explicit conditional hypothesis. It is strong: it already supplies a normalized unit-valued delta coefficient on the whole orbit. The package proves the classical algebraic implication from that hypothesis rather than constructing it. This is permitted and clearly disclosed. It neither quantifies over staircase parameters nor hides the full target as an axiom or premise. The hypothesis has nonvacuous examples over ℤ, including a proper summand of a nonfree module in the independent controls below. At the zero ring the identity is still valid, though it conveys no nonzero-orbit assertion; the general results do not rely on this degenerate case.

## Action, retraction and complement

Source line numbers below refer to the original 200-line `StaircaseSupport.lean`.

1. **Regular coordinates, lines 27–48.** The action is `(h·a)(g)=a(h⁻¹g)`. For a delta function at `k`, it gives the delta function at `hk`. The independent theorem `delta_translation` verifies this over every commutative ring and every group. For finite G, functions `G → R` and finitely supported coefficients on G identify by extending/restricting finite support; the delta basis and left action are those of the left regular module. This mathematical identification is sound, but an equivalence to `MonoidAlgebra` is not present in the author source. Without finiteness, the same coordinate action exists but the whole function module need not be the group algebra; no such infinite regular-module conclusion is advertised.
2. **Orbit and coefficient maps, lines 50–81.** `I(a)=∑g a(g)ρ(g)z` is R-linear, and `P(x)(g)=θ(ρ(g⁻¹)x)` is R-linear. Both equivariance identities are unconditional. In particular
   `P(ρ(h)x)(g)=θ(ρ(g⁻¹h)x)`, while
   `(h·P(x))(g)=θ(ρ((h⁻¹g)⁻¹)x)=θ(ρ(g⁻¹h)x)`.
   This calculation checks the order even for nonabelian G. The orbit-map proof reindexes a finite sum by left multiplication, with the same convention.
3. **Split identity and injectivity, lines 83–114.** Separation gives `P(ρ(h)z)(g)=δ(g⁻¹h,1)=δ(g,h)`. Applying P to the finite linear combination gives `(PI(a))(g)=a(g)`. The source proves equality of linear maps, then derives injectivity from the left inverse. There is no use of regular-module injectivity over a field, division, character theory, or exactness of tensoring an arbitrary injection.
4. **Complement, lines 116–156.** The complement is the actual submodule `ker P` in the whole M. The explicit term `x-I(P(x))` lies there. The proof of `IsCompl (range I) (ker P)` establishes both zero intersection and supremum equal to top, not just a partial decomposition inside the orbit span. Applying P to an element `I(a)` in the intersection forces `a=0`; every x is the sum of the displayed two terms. `range_stable` and `ker_stable` prove invariance under every group element. Neither stability lemma needs separation. The separate equivariance and R-linearity mathematically imply R[G]-linearity in finite coordinates; no bundled R[G]-linear morphism or product `LinearEquiv` is claimed to have been constructed.

All of these substantive README claims pass. The unbundled interface is a genuine coverage boundary, not a semantic error.

## Base change and integer support

At lines 162–181 the exact additional hypotheses are `[CommRing A] [Algebra R A]`, with arbitrary R-modules V,W. In mathlib's pinned `Tower.lean`, `LinearMap.baseChange A f` has the actual type

```
A ⊗[R] V →ₗ[A] A ⊗[R] W
```

and sends `a ⊗ v` to `a ⊗ f(v)`. I checked the definition and composition/identity lemmas at lines 655–689 of that pinned file. Thus `baseChange_split` tensors a **given split identity**, `baseChange_injective` deduces injectivity from the tensored left inverse, and `baseChange_intertwines` tensors a **given intertwining equation**. They assert no preservation of general injections, no identification of a tensored kernel with a new kernel, and no bundled scalar-extended representation. Both original equivariance identities can in fact be supplied to `baseChange_intertwines`; the independent source instantiates both. For R=ℤ, every commutative unital ring has its usual algebra structure, so the advertised arbitrary-ring/nonflat scope of this abstract step is correct. Characteristic restrictions do not occur.

The integer theorem at lines 187–196 has exactly a finite set `s`, arbitrary integer functions d,r, and the hypothesis `∑ i ∈ s, (d i-r i)^2=0`; it concludes equality only at indices in s. The proof uses nonnegative integer squares to obtain termwise vanishing. It makes no inference in an unordered coefficient ring and derives no support, moment or palette hypotheses, global budget, or positive coefficient. Its zero-budget premise is exposed. The README's restrained description is accurate.

## Paper correspondence and omissions

Every entry of `paper-correspondence.json` agrees with the actual types and with the read manuscript snapshot:

- The regular-coordinate description corresponds abstractly to the regular word lattice, but does not construct B, its cardinality, the word orbit or J_m.
- The orbit-map formula and its equivariance correspond to the downstream algebraic map in the candidate §4 and the main theorem proof. They have no Specht instance.
- `coefficientMap` matches the formula in `eq:coordinate`. The equality of that formula with `J_m⁻¹ π_D q^B` is not proved in Lean.
- `eq:product` corresponds to the **assumed** predicate `Separates`; the staircase proof of this product identity is absent.
- After that hypothesis, the split identity, injectivity and invariant complement are genuinely proved.
- The three base-change theorems cover tensor functoriality and preservation of the two intertwiners. They do not identify a base-changed regular coordinate module with A[G], a Specht lattice with its scalar extension, or the tensor-cube reassociation.
- The integer theorem covers only the termwise-zero consequence after `eq:deficit`; it proves neither `prop:unit` nor even the moment/budget calculation which precedes that consequence.

In particular, this package does not formalize triangular palettes, polytabloids or the specified `v_R ⊗ v_R ⊗ v_C`, any all-m instance, the equality filter, the unit sign +1, the construction/existence of a staircase functional, or the main theorem and its multiplicity consequences. The manuscript gate remains separate. The source supports a real general algebraic portion of the intended proof without supplying its load-bearing staircase combinatorics.

## Independent controls and actual rejected mutations

`ReviewSupport.lean` contains 18 theorems, six definitions and two type abbreviations; `ReviewChecks.lean` prints all 26 types/axiom closures. These controls were written for this review, not copied from the author's `Controls.lean`.

- `delta_translation` checks the actual delta-basis convention in full generality. On S₃, the distinct transpositions h=(01), k=(12) satisfy hk≠kh. `right_shift_fails` proves that the coordinate rule `a(g h⁻¹)` gives the wrong answer at g=hk for a=δ_k. This adds a distinction that the author's abelian C₃ examples cannot test.
- The ambient integral module is `(S₃ → ℤ) × ℤ/2`, with regular action on the first factor and trivial action on the second. A literal coordinate functional separates `z=(δ_1,0)`. The actual maps are verified to be `I(a)=(a,0)` and `P(a,t)=a`. The kernel is precisely the torsion factor, contains the nonzero element `(0,1)`, and is complementary to the orbit range. This exercises a proper summand and an ambient module with torsion, rather than another identity map on a free regular module.
- Both intertwiners and the split identity are instantiated after extension to arbitrary commutative ℤ-algebras, then explicitly to ℤ/2 and the zero ring ℤ/1.
- Multiplication by 2 on ℤ is proved injective. Its actual scalar extension to ℤ/2 is proved zero **and noninjective**, using `1 ⊗ 1 ≠ 0`. This supplies a concrete nonflat control: the split result survives the same scalar extension which destroys an ordinary injection. This is not a flatness hypothesis hidden in a positive example.

The author's original six controls also recompile and are correctly described as two positive theorems and four concrete counterexample theorems. They are not failed-compilation mutation tests and they test no staircase combinatorial sign.

In addition, this review performs three real source mutations, each in its own fresh directory with no original support olean on its search path. The mutated definitions and matching application formula are changed consistently; the untouched substantive proofs then fail:

1. Remove the inverse in the coefficient formula. Lean leaves, among others, `θ(ρ(g*h)x)=θ(ρ(h⁻¹*g)x)` and `(∑x, if g*x=1 then a x else 0)=a g` unsolved.
2. Use `a(g*h⁻¹)` for the regular action. The representation multiplication law leaves `a(g*(k⁻¹*h⁻¹))=a(g*(h⁻¹*k⁻¹))` unsolved, and both intertwiners fail.
3. Replace the unit normalization by zero. The split proof leaves `0=a g` unsolved.

All three compiler exits are 1 with semantic `unsolved goals` diagnostics, not import/parser failures. Complete mutated sources are in `mutations/`, with logs in `logs/mutation-*.log`. Rejection of an unchanged proof alone does not establish logical impossibility of every alternative theorem. The independent concrete controls establish the relevant inverse/orientation and nonflat distinctions; the mutation logs establish sensitivity of this implementation. None is evidence for all-m palette uniqueness.

## Compiler evidence and trust

`audit-receipt.json` records eight compilation/check runs: five expected successes with exit 0 and three expected semantic rejections with exit 1. Successful runs have no errors, warnings or `sorryAx`. The independently regenerated author type/axiom and control logs exactly match the originals. The fresh support olean SHA-256 is `dac136d53f03c438b0b3371b70226f009a5510436ed11666c8f59b30443883f5`, matching the author receipt. No existing `StaircaseSupport.olean` was used.

The compiler is Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, executable `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, executable SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. All nine dependency HEADs match the locked revisions; mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`. The complete pins are in the receipt and copied lock. Source and type checks run in a new disposable directory under this review, first compiling the author source and then importing that new artifact. The author's own rebuild script was also run only on the copied package, with `--cache` explicitly pointing to the shared pinned cache.

All 20 original declarations, six author controls, and 26 review declarations have axiom closures contained in `{propext, Classical.choice, Quot.sound}`. The accepted Lean sources contain no `sorry`, `admit`, custom axioms, `unsafe`, or `native_decide`. Finite `decide`, arithmetic tactics, `simp` and reindexing proofs produce kernel-checked terms; the source contains no external oracle or encoded full-target assumption. The imported dependencies and compiler remain trusted setup: I did not rebuild or recursively kernel-check shared dependency oleans, hash their entire transitive import graph, or audit upstream library truth. Git HEAD pins alone do not attest cached artifact contents. No dependency build, network access or cache modification was performed by this review.

The initial reviewer control drafts needed ordinary Lean elaboration/simplifier fixes (decidability, tensor module notation, extensionality and linter warnings, plus parsing the two axiom-free abbreviation reports); these were reviewer-code issues, not author-package failures. The receipt records the final successful source. No incomplete draft is counted as a successful compilation.

## Reproducibility limitation and mitigation

**No current manuscript hash mismatch was found.** The original verifier passed, and the live manuscript was independently hashed again: it remains 15,845 bytes, SHA-256 `015e76c58ebbd6b92c8868d2de9cf49f533f18408e5017b720df8d02f4767495`.

The author's verifier deliberately checks its input manifest against live paths, including that actively authored manuscript. A future edit will therefore fail the strict provenance check even if the Lean source and all formal results are unchanged. That is a snapshot-provenance coupling, not evidence of a formal error. The README already says changed inputs require an explicit new manifest. No repair to the frozen package is required for this audit.

This review supplies the independent mitigation `context/main.tex`, an exact immutable reading copy, and separates frozen-review verification from optional live-input verification. `verify_review.py` verifies the review inventory, copied author package, frozen manuscript correspondence and compiler receipts without needing the live manuscript to remain unchanged. `verify_review.py --live-inputs` additionally checks every recorded repository input against its current path. The latter passed at delivery. The integrator can preserve the original formal package and this snapshot, then issue a separately versioned correspondence manifest if the final manuscript changes; no silent hash refresh is appropriate.

From this review directory:

```
python3 -B run_review.py
python3 -B verify_review.py
python3 -B verify_review.py --live-inputs
```

Rebuilding intentionally refreshes receipts, so elapsed-time fields change; a new output manifest must then be frozen explicitly before integrity verification. The delivered output manifest is self-excluded and records all other review files with SHA-256 and byte lengths. Original author hashes are checked again through the input records and original verifier; the frozen author package is untouched.

## Repairs and optional suggestions

**Required repairs: none for the advertised scoped support.** No mathematical, action-orientation, axiom, compilation, coverage or present integrity defect was found.

Optional integration suggestions are to preserve the frozen manuscript snapshot/provenance separation above, and to bundle regular-coordinate/group-algebra equivalences and the scalar-extended action only if a later formalization needs those interfaces. They are not prerequisites for including this accurately described conditional support. The staircase separation proof, full theorem formalization and full manuscript review remain separate tasks; this verdict awards none of those gates or any acceptance/count credit.
