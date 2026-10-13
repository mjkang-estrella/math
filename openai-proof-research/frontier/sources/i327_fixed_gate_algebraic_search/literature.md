# I327 — source and literature comparison

2026-10-13. Primary-source comparisons only; no full external body retained. Exact raw authentication and reading scope are in `input-authentication.json`.

## Pinned premises

All raw URLs below use [revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

- [Exact factoring introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/01-introduction.tex), `thm:main`: exact finite-gate factoring, polynomial uniformity, gates and qubits. Companion sections 02–06 were read in full: `lem:dyadic`, `lem:records`, `lem:transform`, `lem:majorant`, `prop:order-trial`, `prop:process`, `lem:completion`, `prop:known-probability`, `lem:quarter`, and final reflection proof. The order trial gives a prescribed correct-order mass; the final compiler has explicit canonical witnesses.
- [Quasi-Riemann source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex), `thm:main`, lines 106–111: all Dirichlet L-functions zero-free to the right of 7/8, including zeta with its principal pole allowed. `cor:nonresidues-square-roots`, lines 325–361, already records the quadratic consequence. The main I327 deduction uses the actual Dirichlet theorem, not a conjectural GRH replacement or an audit of upstream truth.
- [Family-142 introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/build/sections/00-introduction.tex), `thm:factorization` and `thm:reduction`; [table](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/build/sections/01-table.tex), `table:construction`; finite-field section `ff:unitroot`; analytic section `analytic:auxiliary`. The input is dense, E is charged numerically, and large-primary construction is not poly(log ell).
- [Primitive-roots companion introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/01-introduction.tex), `thm:hecke-zero-free`: the field/character-uniform 10^-6 strip was inspected as the lead into the stronger direct Dirichlet premise above. Its fixed-base primitive-root theorem varies p, so it does not itself solve every supplied p.

## Exact quantum predecessors

[Muhammad Imran, arXiv:2205.04240v2](https://arxiv.org/html/2205.04240v2), displayed Sections 1–4 read independently. Section 3 uses Mosca–Zalka exact QFT. Section 4 starts with a uniform multiplicative-group state and explicitly rotates an ancilla with squared amplitude m/[2(m-r)]. These operations are not supplied over the source gate ring. The literal gcd merge is insufficiently defined for importing a group-generation proof; the independent repair in the analysis leaves escape preparation as a separate operation. This is a model-specific limitation, not a rejection of exact primitive finding in stronger models.

[Imran–Ivanyos, Quantum Information and Computation 22 (2022), 770–789](https://www.rintonpress.com/xxqic22/qic-22-910/0770-0789.pdf), physical PDF pages 3–5: explicitly distinguishes finite bases, infinite bases, and input-dependent parameters. Theorem 1 charges exact QFT_m oracle calls. Its fixed-modulus finite-basis consequence does not implement growing odd moduli over I327's specific basis. Page 7's primitive-finding corollary also retains QFT oracles and characteristic-dependent or ERH bounds. Neither predecessor establishes the direct fixed-gate completion sought here.

## Classical analytic interfaces and priority limits

[Bennett–Martin–O'Bryant–Rechnitzer, Counting Zeros of Dirichlet L-functions, arXiv:2005.02989v1](https://arxiv.org/pdf/2005.02989), Theorem 1.1 and Corollary 1.2 on PDF page 2: explicit uniform zero counts with logarithmic conductor dependence. Only these statements were relied upon, not their numerical verification tables.

[Kowalski, Arithmetic Randonnee, January 19, 2021](https://metaphor.ethz.ch/x/2021/fs/401-3109-65L/probabilistic-number-theory-fs-2021.pdf), Theorem C.5.6 and ensuing discussion, printed pages 180–181: truncated Dirichlet explicit formula with an absolute remainder and the Mellin-contour mechanism. I327 combines this classical interface with the stipulated zero locations and proves its uniform escape bound separately.

[Grossman, Finding Primitive Roots Pseudo-Deterministically, ECCC TR15-207](https://eccc.weizmann.ac.il/report/2015/207/), primary abstract: records polynomial deterministic primitive search from a supplied p-1 factorization under GRH. It demonstrates the classical ancestry; I327 claims neither its least-primitive-root bound under the weaker strip nor a new assembly technique.

Bach's *Explicit bounds for primality testing and related problems* (1990) was located as the historical subgroup-escape lead, but the AMS PDF was inaccessible (403). No theorem from its unread body is used. Searches and third-party summaries establish no global priority. I322's frozen literature note was context only. Its candidate and bridge remain unreviewed; the bridge arithmetic was checked independently for the supporting unique-order result.

**Contribution verdict:** exact primitive finding follows under the stipulated corpus, but this report is a routine analytic corollary plus the already stipulated exact factorization. No substantial acceptance nomination or new-to-literature claim is made.
