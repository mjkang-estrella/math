# I297 — primary sources and contribution collision

Whole-response hashes authenticate bytes, not reading of whole papers. No full external paper or section is retained in I297. Exact local-file hashes and read extents are in the input authentication JSON; fresh-source metadata are in `source-metadata.json`.

## Decisive old size-five theorem

Timothy Leake, Brian Lins, Ilya M. Spitkovsky, *Pre-images of boundary points of the numerical range*, Operators and Matrices 8(3) (2014), 699–724, DOI `10.7153/oam-08-39`. [Publisher PDF](https://files.ele-math.com/articles/oam-08-39.pdf).

Read actual Sections 1–5, printed pp. 699–718, all theorem statements and proofs; figures not visually read, later sections not read. Main labels: Theorem 2.1, Proposition 2.4, Theorem 3.2, Theorems 4.1/4.4, Lemmas 5.1/5.2, Theorem 5.3, Theorem 5.7, Lemmas 5.8/5.9, Theorem 5.11. Theorem 5.7 restricts an irreducible size-five matrix to at most two multiply generated round boundary points. Its proof distinguishes parallel supporting lines (Lemma 5.8) and nonparallel supporting lines (Lemma 5.9 and the final scalar-compression contradiction). Theorem 5.11 records elliptical arcs/full ellipses among reducible alternatives, so the irreducibility restriction matters.

PDF bytes 629065; SHA-256 `d3519a5aa77b77a586efdfb2cd47cdd8736f628d88cb5d8e5b2e72c4b72a2906`. In-memory `pdftotext -layout` UTF-8 SHA-256 `1f5a95789f035b273a19af35a47b651a694262235d671a411e0107fa06c639bd`. This old theorem already supplies the needed size-five pencil operation. I297's E5 extension is a technical combination with R016, not a nomination of this theorem as new.

## Immutable stipulated OpenAI inputs

- [Direct main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex). Read lines 37–76, 162–452. Labels `thm:main`, `lem:faber`, `prop:coefficients`, `lem:resolvent`, `thm:domain`; `eq:pairing`, `eq:ordered-products`, `eq:weighted-dual`, `eq:diagonal-L2`, `eq:cross-L2`, final positive-block comparison. SHA-256 `54a429fe7129b4760b3015fabf2269d4de5fa38aba9539b18542c1df7e58333f`; Git blob `5976502d77febf477933f36f6205c6e1aa6370ae`.
- [Structural main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex). Read lines 92–147, 863–966, 977–1065. Labels `thm:structural`, `thm:representation`, `eq:fiber-equality` continuation, `eq:positive-block`, `eq:projected-densities`, `lem:comparison`. SHA-256 `8a5de532bd3bd4c0b84cc8114c22175968813a6e984ced0d1bf48011270e621c`; Git blob `2ace452c83a9ceb994a87ae9009441706d90a961`.

Both fresh hashes and blobs match exact entries of `sources/preprints-tree.json`. The direct original-matrix mass-two field is used; the companion's similar-matrix mass-one density is not exchanged with it. All pinned results are stipulated true, without upstream truth audit.

## Nearby equality constraints

[Åhag–Czyż–Virtanen, arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3). Read full completed I246 primary extractions of Sections 5, 7 and 11, including actual statements and proofs. Fresh HTML bytes 1516860; SHA-256 `ce45d2d66da2c73de07a83106b2992894944a447faad00542e25d7b686f4fe57`.

Theorem 5.3 gives orthogonal rectangular supports and a sum-rank dimension bound. Proposition 5.4's top **singular-value** simplicity is stated for specified minimal rectangular cases. Section 7 transfers complete equality to scalar equality through size three. Proposition 11.1 and Theorem 11.2 are scalar polynomial classifications; Corollaries 11.4/11.5 give complete consequences through size three. Later Section 11 inverse-algebra consequences also are scalar and require their stated hypotheses. These operations do not identify constant compression of a specified P in dimension five. The all-dimensional rank ceiling in I297 is compared with their sum-rank bound, but no literature-wide novelty assertion is made.

## Credited scalar geometry and interpolation

[Shanmu Jin, *Rigidity at the Extremal Crouzeix Constant*, v2](https://www.preprints.org/manuscript/202609.0079/v2), posted 15 September 2026. Live versioned page redirects to the base page and confirms v2. Reread the completed I246 retained primary file at physical lines 1–80, 185–287, 621–653: introduction/Theorem 1, the end of Proposition 1 and equality data, all of Lemma 4 and its proof, and final Section 8 proof/Corollary 1. The source-labelled extents are L93–166, L271–373, L707–738; intermediate dependencies of the final theorem are credited via the completed review, not newly audited in full.

Theorem 1 supplies scalar disk rigidity only after an actual scalar channel has been extracted. Lemma 4 supplies uniqueness of finite contiguous scalar jets at minimum Schur norm one and the finite Blaschke form. The use is exactly the reviewed R016 scalar completion. Retained primary-file SHA-256 is in the manifest; no new source excerpt is copied here.

## Old six-dimensional geometry and lower bound

[Ben Lawrence, *Examples for the Quantum Kippenhahn Theorem*, arXiv:1809.02779v2, Section 4](https://arxiv.org/html/1809.02779v2#S4). Fresh HTML bytes 834407; SHA-256 `fc158711eee63ea9ffcf90d501799b92b3452d7fc7ade2e30d7b02834b2ae269`. Entire Section 4 read in memory: Lemma 7/proof, LSS family with its parameter constraints and normalization, quantum tensor quantization and discriminant argument. The tensor pencil changes the problem; it is not a one-variable equality compression theorem.

Original Li–Spitkovsky–Shukla, *Equality of higher numerical ranges of matrices and a conjecture of Kippenhahn on Hermitian pencils*, Linear Algebra and its Applications 270 (1998), 323–349, [DOI](https://doi.org/10.1016/S0024-3795(97)00251-6). Original full text not newly obtained. Lawrence is the read reproduction; completed I292 records the original publisher access failure. No negative assertion about the inaccessible article is used.

R019 and its I287 proof supply the actual attained polynomial witness and constant-compression obstruction in dimension six, not merely the old repeated ellipse. I287 SHA-256 `8f8eb9a51203ec949356a1e92913447b56766e68496ec2384003c24430bbcd0b`; completed I291/I292 reviews confirm its proof and original contribution. No new novelty is assigned to the old matrix, disk, inner factorization or that accepted witness.

R016/I242 SHA-256 `03c0f05cef564e1bde2630ed725ff755d3bb603ea07dbd39a711e595e96d6627` supplies the already-paid dimension-free inverse method. Its Sections 1–3 were read at the actual proof level; its size-four step is not extrapolated to five without the old theorem above.

The exact dimensional threshold follows from these two accepted project mechanisms plus the old size-five theorem. The ancillary all-dimensional rank ceiling is unreviewed and not nominated here. No new count, worldwide priority, strict scalar-supremum gap, or size-six disk classification is claimed.
