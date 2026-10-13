# I272 source identities, primary comparisons and limits

Date: 2026-10-12. Target I271 SHA256 `a3ecaddeec1745579ca729e7d2d1e9067c9d97006169a1df0eedfa1361fb54fa`. Verdict TECHNICAL, contribution only. The immutable OpenAI/math revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; all its results are stipulated true. No source truth audit or absence-based novelty claim is made.

## Freshly authenticated pinned source sections

Every file below was fetched from its exact pinned raw URL, matched byte-for-byte to the corresponding I266 retained file, and read in full. Each retained TeX file is one complete source section, not a paper or source-tree snapshot. The introduction files were fully read from the I266 bytes; equality action, compactness and rigidity were fully read from the newly fetched identical bytes. Detached SHA256, bytes and line counts of all retained excerpts are in input-authentication.json.

Matrix base:

`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/`

- [sections/introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/sections/introduction.tex), retained `matrix-introduction-primary.tex`, complete: `thm:main`, `eq:potential-class`, `eq:main-bound`, `eq:extremal-potential`. SHA256 `72dedb3dd3e00cd1e9e3db45c1bc9080f42006ff654cea6a18a98537528a8b60`, 5,720 bytes. The embedded `notes/history` input was NOT expanded.

The actual theorem quantifies over every exponent 1/2<s<3/2 and every finite matrix size, with ordinary unnormalized trace and arbitrary measurable positive Hermitian W satisfying integral tr W^(s+1/2)<infinity. Its exact constant is the C_s used in analysis.md. This quantifier, rather than a catalogue summary, authorizes optimizing s.

Equality base:

`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/`

- [sections/introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/sections/introduction.tex), retained `equality-introduction-primary.tex`, complete: `thm:main`, `intro:classification`, quantitative-defect discussion. SHA256 `296070a983ced0094a761b41562a7eda1e24471d885b84118c3a56227b35b002`, 8,251 bytes.
- [sections/rigidity.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/sections/rigidity.tex), retained `equality-rigidity-primary.tex`, complete: fixed left/right subspaces, Riccati profiles, realification and converse; particularly `rig:factorization`, `rig:partner`, sole-negative-eigenvalue and exact cost calculation. SHA256 `d9deee77f0feb5567f1e19301880d085ce2e273bf916a8a06614e3011a60678e`, 12,542 bytes.
- [sections/action.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/sections/action.tex), retained `equality-action-primary.tex`, complete: `act:quantitative-action`, `act:constraint`, `act:trace-deficit` and all presented proofs. SHA256 `3acbaec3c554c27baf29b98c326a85d7337008a23c839920cd3e773b4c89c32a`, 12,438 bytes.
- [sections/compactness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/build/sections/compactness.tex), retained `equality-compactness-primary.tex`, complete: `comp:relations`, `comp:vanishing-errors`, `comp:tail-bounds` and all presented equality-limit arguments. SHA256 `910c2aea5e27a4ec1f6e46b0dc8f102db0e2faacb057a8c64db8967b328cab8e`, 15,316 bytes.

These sections classify exact equality in the full finite-matrix class and supply the fixed soliton gap. The quantitative action defects are auxiliary; the compactness tail bound contains the physical m factor. No physical J/full-deficit corollary is stated in these read sections. Preambles, bibliography, appendices, preliminary and spectral-bound sections, other matrix proof sections and the scalar companion were not independently read in I272. Their stipulated results are not audited. No claim is made about absence of a statement in unread sections.

## Fresh external primary reading

Short transcriptions and original notes are retained in `classical-primary-excerpts.md`. Full HTML/PDF bytes were used in memory or temporary reading files and were not retained as unread papers. HTML formulas were read via original MathML alttext. All temporary extracts were fully read before removal, except the explicitly defective author-hosted HLW extract below.

1. [Carlen–Frank–Lieb v2](https://arxiv.org/html/1301.5032v2), full HTML identity: 516,987 bytes, SHA256 `bb2338199f11df1fad28aae86fbba026973e66671bd5a5435c3b1111029f8ccc`. Read all Sections 1–2 and 5, including their presented proofs. The comparison is scalar lowest-eigenvalue stability and local-to-global methodology, not matrix orientation/full-sum control. Sections 3–4 and references were not read. Remark 5.2's open-problem language is historical, not asserted current.
2. [Leng v1](https://arxiv.org/html/2606.03749v1), full HTML identity: 222,641 bytes, SHA256 `bc14b2e6951e2a8f34b985cde2b7fc9195a910854244ad4e3d333c50f8640e3e`. Read Section 1's spectral part through Theorem 1.2 and its discussion; Section 2's setup, Lemmas 1–4 and complete proof of 1.2. The statement concerns scalar induced-density distance. The extraction also included, and I read, the short geometric Lemma 5; it supplies no review premise. Theorem 1.3 and its proof, remaining geometric material and references were excluded. This VERSIONED HTML hash differs from I266's unversioned HTML metadata; no false equality of those different retrievals is claimed.
3. [Read–Schulz v2](https://arxiv.org/html/2609.10478v2), full HTML identity: 437,000 bytes, SHA256 `8bbb584cc1593ded2f8de860097a0f6562bc54c4cef8db8de3143771adefb884`. Read the complete introduction and mathematical Section 2, including Proposition 4, (2.1), Lemmas 5–6 and all presented proofs through Proposition 4. It supplies sharp operator-valued gamma=1 control, not the sharp lower-exponent family or stability. Section 1, acknowledgments/AI/funding sections and references were not read. A v1 web introduction was inspected first; the substantive operator comparison uses v2. The current arXiv record lists v2 dated 2026-09-14.
4. [Hundertmark–Laptev–Weidl arXiv primary](https://arxiv.org/pdf/math-ph/9906013), full PDF identity: 150,290 bytes, SHA256 `1d77d78efc33de347555e568939a07254af8fae4cba0cbf48d64ab44c0bdbfca`. Read physical PDF pages 3–8 with intact mathematical extraction: conventions, Theorem 3.1 and complete proof, majorization/monotonicity, Section 3.4, Corollary 3.5 and complete beta-integral lifting proof, and initial Section 4 setup. Remaining pages were not read. The endpoint theorem is credited; its lifting is not I271's exponent minimization. The author-hosted PDF at https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf was also downloaded: 1,192,425 bytes, SHA256 `1e8aac1f8d388ae8e53dfeffd04736a0e00da6b26db6b618023a25d1ffb7f2c1`. Its pages 3–6 text omitted formulas, so no intact fresh theorem reading is claimed for that extraction. The arXiv copy repaired that access limit.
5. [Frank–Gontier–Lewin v2](https://arxiv.org/pdf/2109.05984v2), full PDF identity: 568,432 bytes, SHA256 `60acd2e41f7cb4b5f06c78f0d278329ba84a08ed57eabe9f3a363fa71c27c81a`. Read physical PDF pages 5–10: all Section 2 main statements, plus the preceding introduction ending and following Section 3 opening. These are scalar finite spectral-rank optimizer results. Proofs elsewhere were not read. The latest arXiv record lists v2 dated 2023-05-11; the downloaded unversioned PDF has this matching identity.

Aizenman–Lieb's original 1978 article was not fetched/read. Its method was examined through HLW's actual presented lifting proof; no exact I271 exponent-optimization precedent is attributed to the unread article.

## Bounded current search screen

Fourteen queries were performed on 2026-10-12:

1. `"Lieb-Thirring" "matrix" "stability" equality`
2. `"operator-valued" "Lieb-Thirring" stability equality`
3. `"Lieb-Thirring" "stability" "exponent" ground state`
4. `Read Schulz 2026 sharp Lieb Thirring operator valued gamma 1 arxiv`
5. `"Lieb-Thirring" "stability" "matrix-valued"`
6. `"Lieb-Thirring" "optimizing" "exponents"`
7. `"Lieb-Thirring" equality stability 2026 Leng`
8. `"Lieb-Thirring" "Schulz" "Read"`
9. `"Lieb-Thirring" "stability" "operator-valued" deficit`
10. `"Lieb-Thirring" "stability" equality quantitative 2026`
11. `Aizenman Lieb 1978 semi classical bound eigenvalues Schrodinger sharp constant moment monotonicity pdf`
12. `"Lieb-Thirring" "exponent" "deficit" stability`
13. `"New bounds on the Lieb-Thirring constants" arxiv`
14. `"On semi-classical bounds" "Aizenman" "pdf" princeton`

Secondary search results were leads only. No theorem claim relies on them. A Princeton author-site fetch returned HTTP 403, so no original Aizenman–Lieb text was obtained there. This screen is limited and does not establish absence, novelty or worldwide priority. It found no authenticated exact physical J theorem; the TECHNICAL verdict instead rests on the explicit complete reduction in analysis.md.
