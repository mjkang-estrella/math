# I323 — primary dependencies and comparison boundaries

2026-10-13. This is the source ledger for an independent proof audit, not a contribution review. Pinned OpenAI statements are stipulated true; their interfaces were read directly.

## Pinned exact-factoring source

Root: `preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

- [01-introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/01-introduction.tex): read lines 1–129. Theorem `thm:main`, lines 10–12, states uniform polynomial-size probability-one factoring and the fixed gates. Lines 27–41 distinguish computed-rotation/external-order interfaces. Lines 53–91 credit amplification, phase kickback and four-phase predecessors. SHA256 `6d001bb685b08498db9cf76aa31acb99c28928606025ca746ffa114eeb5be7cc`.
- [02-model.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/02-model.tex): read all 39 lines. Gate/control conventions, reversible arithmetic, Lemmas `lem:dyadic` and `lem:records`, and the fresh-register/old-work interface were checked. SHA256 `4cb63e05a10dc55fcc8e9c978af9fc99d74d24bfb663414f73328b122b0e13ac`.
- [03-order-transform.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/03-order-transform.tex): read lines 1–190, especially `lem:transform`, lines 56–130. Its actual all-zero ancillary branch, phase sign, polynomial shifts and scratch cleanup supply the candidate's transform. SHA256 `b9e0f9184c4e1646d82e6186d923dcfc66c0d2b0a06b5f7c15a94c96c0a4bf31`.
- [06-exactness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/06-exactness.tex): read all 137 lines. Lemmas `lem:completion`, `lem:quarter`, retained-prefix reasoning in `prop:known-probability`, and the final exact reflection identity were checked for the interfaces used. SHA256 `e80b0ef8bac48a380a2d906fa97baf5b55caec7e9dcaac05f9552dff1959a25a`.

The source truth was not audited. The internal I322 bridge was audited separately and is not part of the stipulated corpus. Source raw bodies were not retained.

## Classical counting

[Barvinok–Pommersheim, An Algorithmic Theory of Lattice Points in Polyhedra](https://library.slmath.org/books/Book38/files/barvinok.pdf), Theorem 4.4 and Algorithm 5.2, printed pages 109–112 (zero-indexed PDF pages 19–22), directly support polynomial binary-time counting for fixed-dimensional rational polytopes. The generating function has polynomially many rational terms; Algorithm 5.2 evaluates the finite count by residue coefficients. The relevant body and surrounding proof were read; the whole chapter was not. Raw response: 862363 bytes, SHA256 `bd803c27b438e3803db0e2b8fa4194e1102daca5176a94df3852762d7f5d465d`. The weighted reduction is I322's independently checked binomial lift, not an extra theorem attributed to this source. No PDF or extracted section was saved.

## Exact discrete-logarithm predecessor

[Mosca–Zalka, Exact quantum Fourier transforms and discrete logarithm algorithms, quant-ph/0301093v1](https://arxiv.org/html/quant-ph/0301093v1): independently read the mathematical body, Sections 1–5, especially 2.1, 3, 3.1 and 4.2. Their exact discrete-logarithm construction uses an exact transform; their parameter computation and probability adjustment include rotations with computed angles. Section 3.1 leaves efficient calculation of its direct averaged discrete-logarithm success rate unresolved. This is a specific interface comparison, not evidence against all later fixed-gate work. No raw HTML hash is claimed and no body is retained.

The proof PASS gives no worldwide priority or contribution verdict. Older phase kickback, four-phase approximations, Shor, dyadic sampling, ordinary amplification and prime-power reductions keep their original credit. Prior discovery brief descriptions are task context only; no verdict on this candidate is inferred from them.
