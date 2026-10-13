# I266 source contracts and literature limits

Target: authenticated I264, SHA256 `a0080234eacf4d410917e426222e3e89b24f9eba968cc815c4b46c5b59957395`. Verdict: TECHNICAL, contribution gate only. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Search absence is not used as novelty evidence.

## Freshly read pinned primary contracts

The following exact raw files were freshly retrieved and matched byte-for-byte by SHA256 against I261's authenticated records. Each retained `*-primary.tex` is the entire indicated, fully read section file, not an entire paper. Exact URLs, bytes, SHA256 and prior git-blob identities are in I266's input-authentication.json. Embedded inputs, appendices and bibliographies not listed here were not read by this review.

Equality family base:

`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/`

- `sections/introduction.tex`, full: `thm:main`, sharp full matrix bound and constant-unitary equality classification; quantitative-defect discussion. Retained as `equality-introduction-primary.tex`.
- `sections/action.tex`, full: `act:quantitative-action`, `act:constraint`, `act:trace-deficit`, and both presented proofs. Retained as `equality-action-primary.tex`.
- `sections/spectral-bound.tex`, full: `bound:sharp`, complete spectral passage by finite-list exhaustion and realification. Retained as `equality-spectral-bound-primary.tex`.
- `sections/compactness.tex`, full: `comp:relations`, `comp:vanishing-errors`, `comp:tail-bounds` and complete presented equality-limit argument. Retained as `equality-compactness-primary.tex`.
- `sections/rigidity.tex`, full: fixed subspaces, Riccati classification, realification/converse, `rig:factorization`, `rig:partner` and the sole-negative-eigenvalue calculation. Retained as `equality-rigidity-primary.tex`.

The action estimate retains dimension-independent auxiliary defects but does not state a physical J-versus-D inequality. The compactness argument has physical-dimension factors and is at exact equality. Rigidity supplies the gap and explicit partner factorization used in the direct comparison; no upstream correctness audit was performed.

Matrix family base:

`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/`

- `sections/introduction.tex`, full file: `thm:main`, including every open-range exponent, every finite m, arbitrary measurable positive matrices and the trace-power condition. Retained as `matrix-introduction-primary.tex`. Its `notes/history` input was NOT expanded or read.
- `sections/spectral.tex`, full: `lem:form-compactness`, main-theorem proof, full-list exhaustion, complex realification and sharpness calculation. Retained as `matrix-spectral-primary.tex`.
- `sections/action-framework.tex`, full: `thm:action` and comparison with the scalar method. Retained as `matrix-action-framework-primary.tex`.
- `sections/action-limit.tex`, full: complete presented action proof and penalty limit. Retained as `matrix-action-limit-primary.tex`.
- `sections/field.tex`, full: field regularity/properties/comparison and all presented proofs. Retained as `matrix-field-primary.tex`.

Trace and path proof sections were not freshly read; their theorems invoked within the read sections remain stipulated inputs. No statement from their unread proofs is used for an overlap claim. The main theorem's simultaneous exponent quantifier is essential: applying it at a strictly lower exponent s to the target-gamma profile is allowed because it has no optimizer restriction on its potential. That supplies a full-tail o(J) bound under J-only smallness, as derived in analysis.md.

## Freshly read external primary comparison

[Carlen–Frank–Lieb, v2](https://arxiv.org/html/1301.5032v2), *Stability estimates for the lowest eigenvalue of a Schrödinger operator*: full HTML identity, 516987 bytes, SHA256 `bb2338199f11df1fad28aae86fbba026973e66671bd5a5435c3b1111029f8ccc`, matches I261. Fully read Sections 1–2, including Theorems 2.1, 2.2, 2.5, 2.6 and the presented proof of 2.2; and all Section 5, including Theorem 5.1, Lemma 5.3, Theorem 5.4 and their presented proofs. HTML MathML alttext was extracted intact. Sections 3–4, references and the full paper were not read in this review. The statement quoted as an open problem in the 2013 text is historical; it is not asserted current in 2026.

Only short original reading notes and formula transcriptions remain in `classical-primary-excerpts.md`; temporary full-section extraction files were removed after the complete read. Theorem 2.2 is scalar lowest-eigenvalue stability. Section 5 provides methodological precedent for centering, linearized nondegeneracy and remainder absorption, but no matrix orientation/full-sum theorem. The explicit gap-and-projection comparison in I266 is an independently derived elementary observation, not an asserted CFL matrix corollary.

## Inherited, not freshly reread, external comparison records

I261's `classical-primary-excerpts.md`, literature and input-authentication.json were fully read. These retain the following earlier original-text extents:

- [Hundertmark–Laptev–Weidl](https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf), Theorem 3.1: I261 visually read PDF pages 3–6, operator conventions and complete presented proof. Full PDF SHA256 `1e8aac1f8d388ae8e53dfeffd04736a0e00da6b26db6b618023a25d1ffb7f2c1`, 1192425 bytes. I266 did not retrieve/render/reread this PDF. The endpoint theorem in I264 is credited classical mathematics, but is not an input to I266's alternate closure.
- [Leng](https://arxiv.org/html/2606.03749): I261 read introduction and the spectral theorem/proof through Theorem 1.2, not later convex-geometric proofs. Recorded HTML SHA256 `9ceab1db1c5edce2c5815bf4cd35dadd4d3f29290a86c4c6f1dcf37de4faaffa`. I266 read only the inherited notes/record, not the original text. No fresh overlap theorem is asserted from unread portions.
- [Frank–Gontier–Lewin](https://arxiv.org/pdf/2109.05984): I261 read arXiv PDF pages 5–10, Section 2 main statements, not proofs elsewhere. Recorded PDF SHA256 `60acd2e41f7cb4b5f06c78f0d278329ba84a08ed57eabe9f3a363fa71c27c81a`, 568432 bytes. I266 read only the inherited notes/record. The source concerns scalar finite-rank optimization in that record; no new original-text comparison or full-paper read is claimed here.

Those identities are inherited provenance, not hashes of fresh downloads by I266. The records do not establish exhaustive absence of a matrix/vector stability theorem. Neither a generic scalar-to-vector extension nor a theorem about the entire negative spectrum is silently attributed to them.

## Bounded current search screen

On 2026-10-12 the six queries were:

1. `"Lieb-Thirring" "stability" "matrix" quantitative`
2. `"Gagliardo-Nirenberg" stability vector valued Hilbert quantitative`
3. `"1301.5032" stability eigenvalue`
4. `"matrix-valued" "stability" "Lieb-Thirring" deficit`
5. `"operator-valued" "quantitative stability" Schrödinger`
6. `"Hilbert-valued" "stability" "Gagliardo"`

These produced CFL, scalar GNS stability leads, stability-of-matter and generalized magnetic LT material, bibliographic/secondary results and unrelated hits. Search snippets were treated as leads only. The CFL original text was actually fetched/read as specified above. No other new original theorem contract was authenticated from these searches, and none is a premise in the verdict. The scalar GNS leads were not assumed to have or lack a Hilbert-valued extension. No relevance score, absence-based novelty claim or worldwide priority conclusion is made.

## Contribution comparison

No read source explicitly states I264's exact D-versus-J theorem. The TECHNICAL verdict instead rests on a positive derivation covering all its quantifiers: an exact scalar-ground-state Hilbert decomposition bounds the nonlinear lowest-energy loss, an elementary partner-factorization comparison compresses the tail, and the stipulated matrix theorem at a lower exponent plus weighted Hölder makes that tail o(J). This matches the claimed intermediate power without small supremum or HLW. Exact candidate constants and domains remain the separate proof gate.
