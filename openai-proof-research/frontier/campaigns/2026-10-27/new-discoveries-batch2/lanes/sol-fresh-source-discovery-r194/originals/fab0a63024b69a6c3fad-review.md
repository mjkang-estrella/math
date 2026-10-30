# Independent review: quadratic differences and symplectic orbits

Decision: **PASS for both complete primary-source counterexamples**, with the existing-result and source-correction qualifications below. Reviewed on 2026-10-26 by the discrete/Fibonacci lane, which did not author either artifact. No candidate artifact, shared index, or git state was edited by this reviewer.

The authoritative integrated outcomes reviewed are `thirty-proof-campaign/outcomes/quadratic-difference/` and `thirty-proof-campaign/outcomes/symplectic-orbits/`. Both Lean files match their originals under `extension-matrix-second/` byte for byte. The final parent-formatted papers were read in full.

## Exact reviewed hashes

| Outcome | Reviewed file | SHA256 |
|---|---|---|
| MathDB 358595 | `formal/QuadraticDifference.lean` | `9b8889328b4c3faa365a927faee07afa532a0e4be7b7ae5f7c68c7352512c457` |
| MathDB 358595 | final `main.tex` | `58ec7e1f37c5b8ac0633c716e7635ee3769c0f7cad49cee8eba57354ee108f55` |
| MathDB 381863 | `formal/SymplecticOrbits.lean` | `9348ab387a50ca8776a70eaad4e2a8db1d1d70ede3313908686969647517b579` |
| MathDB 381863 | final `main.tex` | `240b153453a0a4dba80477ce008b03232fc886db291e66773aeb7eb1f4276e75` |

This is mathematical/formal/source-scope review. Authored-PDF generation and visual QA are the parent's separate step.

## Independent fresh verification

Copied the exact integrated manifests and Lean sources into unique scratch outcomes under `extension-discrete-second/review-matrix-second/`, then ran `twenty-proof-campaign/verify_outcome.py` independently on each copy.

Both audits **PASS** with warnings treated as errors, pinned Lean 4.34.1, and verified dependency revisions:

- Quadratic differences: **26 declarations**, main theorem `QuadraticDifferenceCounterexample.source_endomorphism_counterexample`.
- Symplectic orbits: **45 declarations**, main theorem `SymplecticOrbitCounterexample.source_counterexample`.
- Each audit reports only `propext`, `Classical.choice`, and `Quot.sound` as foundational dependencies.

Fresh logs/receipts are in the two scratch `build/` directories. Additional `ScopeChecks.lean` checks independently verify the matrix/endomorphism B-alternating predicate bridge and surjectivity, the strict increasing order and exact pair coverage of all six deletion maps, and completeness of the one-/two-element subsets of the three source coordinate pairs. The candidate's finite integer Pfaffian equalities are proved by ordinary kernel-checked `decide`, not an external or trust-expanding evaluation mechanism.

## MathDB 358595: ordinary versus symplectic quadratic differences

### Primary-source fidelity

Read the actual archived primary manuscript text, arXiv:2305.19340v1, Section 1.1 (field and finite-dimensional-space conventions), Section 1.2 (monic quadratic p,q and ordinary difference), Definition 1.1 (symplectic pair and symplectic difference), and Section 1.3's Conjecture 1 plus the immediately following disproof.

The source explicitly defines an endomorphism u to be b-alternating when the bilinear form `(x,y) ↦ b(x,u(y))` is alternating, equivalently `b(x,u(x))=0` for every vector. Thus the code's predicate is the actual source notion; it is not the different condition of being skew-adjoint or preserving b. The source permits arbitrary monic degree-two p,q and arbitrary fields; it does not require p,q distinct or split. The choice `p=q=X²+1` over ℝ is admissible.

The paper correctly says that this conjecture is already disproved in the source. Its real-plane example specializes the author's irreducible-quadratic counterexample family with odd half-dimension one; it is not a fresh resolution of an open question.

### Full formal construction and bridge

`b` is an actual `LinearMap.BilinForm ℝ (Fin 2 → ℝ)` constructed via `Matrix.toBilin' J`. `form_eval` proves its exact coordinate formula. `form_alternating` and `form_nondegenerate` establish the symplectic form conditions; the latter derives nondegeneracy from the actual nonzero determinant. The zero endomorphism satisfies the source's b-alternating condition.

The polynomial is actually monic with natural degree two. The explicit rotation J satisfies `aeval J p=0` because J²=-I. Using it twice gives the ordinary zero difference. For an arbitrary candidate b-alternating matrix M, evaluating its diagonal bilinear expression at `(1,0),(0,1),(1,1)` forces M to be scalar. Its polynomial value has diagonal entry `α²+1`, which cannot be zero over ℝ. This rules out all b-alternating roots, hence all symplectic decompositions of zero.

The final theorem is on **actual `Module.End` objects**, not only matrix labels. `Matrix.toLinAlgEquiv'` is an algebra equivalence preserving scalar polynomial evaluation; `root_end_iff` explicitly proves the needed root transport. Its surjectivity is used in the nonexistence proof, so no possible linear endomorphism is excluded from consideration. The review's independent scope checks also instantiate both this surjectivity and the definitional equivalence of the two B-alternating predicates. Finite-dimensionality of `Fin 2 → ℝ` is intrinsic to this concrete admissible vector space.

No source-form membership, root condition, or endomorphism bridge is assumed as an unproved hypothesis. The theorem fully exhibits ordinary difference and failure of symplectic difference for an admissible symplectic pair.

### Written proof and credit

The final TeX proves the coordinate classification of alternating endomorphisms and explains the complete endomorphism transport. The archived MathDB solution `219c8ab7-7563-4bfb-93bb-742feca6ee31` is by Clément de Seguins Pazzis and points directly to the source's existing counterexample. Recomputed its body hash and every source snapshot hash; all match `source.json`. The paper and metadata credit that author and deny discovery, priority, or first-formalization claims. There is no attribution blocker.

## MathDB 381863: insufficient Pfaffian invariants for symplectic congruence

### Correct primary domain, standard form, and action

Read the actual arXiv:2212.08360v1 manuscript text in Sections 1.2 and 7, Definition 2.12, Theorem 2.8, and Section 9 Conjecture 1. The primary source defines

`S(2n,ℝ)={A : Aᵀ=-A and det A≠0}`,

with J the **interleaved block diagonal** of copies of `[[0,1],[-1,0]]`. Its group is exactly `Pᵀ J P=J`, acting by `A ↦ Pᵀ A P`. These match the code. In particular this is not a theorem about symmetric matrices; the package accurately identifies and corrects MathDB's transcription error. Both A0,A1 satisfy the actual primary skewness and nonsingularity hypotheses, and both are proved not to be any scalar multiple of J, as the source conjecture requires.

### Exact invariant construction, including normalization

The source's proposed `s_k` sums Pfaffians of principal submatrices obtained by deleting **complete adjacent coordinate pairs** `(1,2),(3,4),(5,6)`. It is not the sum over all arbitrary principal submatrices.

The code defines the full signed permutation formula `sourcePf`. Its zero-based factors `(2i,2i+1)` correspond exactly to the source's one-based `(2i-1,2i)`. At n=3, `rawInvariant` covers all source cases:

- k=0: the full 6-by-6 matrix;
- k=1: the three increasing retained index lists `(0,1,2,3)`, `(0,1,4,5)`, `(2,3,4,5)`;
- k=2: the three increasing retained pairs `(0,1)`, `(2,3)`, `(4,5)`.

These enumerate each allowed deletion once, with the inherited order and no skipped or extra submatrix. The independent scope checks prove all six maps are strictly increasing, verify their ranges against retained/deleted pair indices using integer division by two, and enumerate all size-one and size-two subsets of the three pairs.

Definition 2.12 indeed prints an all-permutation Pfaffian sum without the usual factor `1/(2^m m!)`. The artifact does not silently choose a different normalization: `raw_invariants_equal` proves equality for that literal printed sum, while `invariant` and `pfaffian` include the standard normalization. `invariant_zero`, `invariant_one`, and `invariant_two` prove the exact bridges to the three sums of normalized Pfaffians. Since all summands for fixed k have common size `2(3-k)`, the normalizing factor is common; equality holds with either convention.

The finite computations are performed first on the exact integer matrices `A0Z,A1Z`, and `sourcePf_cast`, `rawInvariant_cast`, `A0_cast`, and `A1_cast` prove transport to the displayed real matrices. No list of characteristic coefficients, assumed spectral data, or replacement polynomial is used as a proxy for the actual invariants. Both raw and normalized equality are theorem consequences, and the source formula ambiguities cannot change this counterexample.

### Full noncongruence and nondegeneracy

Both matrices are exactly skew. Explicit inverses give right-inverse identities, whose determinants prove `det A_i≠0`; this avoids relying on an assumed Pfaffian-determinant identity or approximate rank computation. Individual entries rule out scalar multiples of J.

For the orbit obstruction, `J_squared` proves J²=-I. Assuming a source symplectic congruence, the proof constructs `L=-J Pᵀ J` and proves both `LP=I` and `PL=I`. It then proves the actual transformation rule `K1=L K0 P` for `K_i=-J A_i`. The polynomial `(K0-I)(K0-2I)` vanishes; the corresponding expression at K1 has a nonzero `(0,2)` entry. Factoring under the proved similarity and cancelling `PL` forces it to vanish, a contradiction. This rules out every P satisfying the source group and action equations; it does not merely compare a selected family of transformations.

The final theorem proves every admissibility hypothesis, equality of every invariant k=0,1,2, and absence of symplectic congruence. This is a full counterexample to the primary-source orbit conjecture.

### Written proof and prior credit

Read the final complete TeX, including its matching interpretation of the Pfaffian equality and exact quadratic-polynomial orbit obstruction. It accurately states the skew/symmetric correction and both normalization conventions. It credits the matrices to Shivam Patel's posted counterexample, using a local polynomial obstruction instead of the post's eigenspace-dimension computation. The source body and snapshot hashes all recompute correctly; the posted solution is `fe50c06f-f1b5-48c5-81d3-8a4d9a733bb7`. No new mathematical discovery or worldwide first-formalization claim is made.

## Final assessment

**PASS: MathDB 358595** is a full formal verification of an already published primary-source counterexample, including the actual bilinear form and arbitrary linear endomorphism quantifiers.

**PASS: MathDB 381863** is a full formal verification of Patel's existing counterexample to the primary-source nonsingular skew-form classification. Preserve the correction from MathDB's symmetric wording and the raw/normalized Pfaffian note when describing the outcome.

No unresolved mathematical, formal-coverage, source-fidelity, or attribution objection remains at the exact hashes above.
