# Source contracts, provenance and actual reading

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Every pinned path below is relative to `preprints/` in
[openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
`inputs/pinned-records.json` gives the full path, exact retained size,
SHA256, and Git blob SHA1 for EACH of the 15 retained TeX blobs. Raw
retrieval used
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.
Each blob was checked against the COMPLETE snapshot tree by computing
SHA1 of `blob <byte-length> NUL <bytes>`. This proves byte identity and
catalogue membership, not semantic comprehension or upstream truth.

Use T for `A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/build/sections/`,
AR for `An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/build/`,
Q for `Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/build/sections/`,
and E for `Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/build/source/sections/`.
All these are private source reading copies, not original licensed prose.

## Selected dependency family and exact interfaces

- T/introduction.tex, blob `1c1c4f98074f32148f5077da2865ebc23203b55e`:
full 357 lines read, including `thm:main`, `cor:homological`,
`cor:finitistic` and the warning about the algebraic closure's parameters.
The main theorem supplies the generic symmetric example, used for the
finite-window deduction. The consequences are read for duplicate checking,
not proposed as new results. No proof audit of the theorem is claimed.
- T/algebra.tex, blob `3a7b197ff4f2ead4e6f676d64131dcc4da6e1c89`:
full 339 lines read. `a:multiplication`, `a:table`, `a:radicals`,
`a:dual-dimensions` and `a:resolution`, including their displayed proofs,
are the actual starting interfaces. New finite-order ranks and homology
are independently deduced from the table; the source asserts the generic
resolution only. Its coefficients 1+q^{i+2} and 1+q^i must stay nonzero.
- T/stable.tex, blob `d64c3b8dc60713211bb32deb3d34fa73d87b2a77`:
full 319 lines read, including statements and proofs `e:polynomial`,
`e:all-degrees`, `e:socle`, `e:twists`. Positive Hom is polynomial in
classes of degree three, negative Hom is its shifted dual; the twist
weights are H^{-m} and H^{m+2}, respectively. The conditional comparison
uses only these actual weights, not an inferred action of H=0.
- T/triangular.tex, blob `04bef4ebcee21dfd9aae285f56e1a43704eeef19`:
full 320 lines read, including `t:fiber-hom`, `t:comparison-maps`,
`t:finite-module`, `t:vanishing`, `t:end-cohomology`, and the theorem's
completion. The cone exact sequence is available before invertibility is
used to kill its ends. It licenses the CONDITIONAL singularity deductions
when the altered construction retains all its earlier hypotheses.
- T/transfer.tex, blob `0ffb43fdacb838920d5e407effd34301e6291ab9`:
full 132 lines read, including `tr:trivial-symmetric`, `tr:transfer` and
the proof. The transfer requires a totally acyclic finite-projective
resolution and H^a Hom(P,Z)=0 for a>0 AND a<=-2. Only positive vanishing
is insufficient for this ordinary symmetric trivial extension.
- T/homological.tex, blob `86b7bfafaf7bfc1cddca4b06248118540d545ff8`:
lines 1--78 read (including `h:comparison` and its proof beginning);
other labels were searched for location. Full 466 lines authenticated,
NOT read in full. The comparison statement identifies positive full-Hom
cohomology with Ext for a totally acyclic source and exact projective
target. No new proof of its general source interface is claimed.
- T/bimodule.tex, blob `22d686a1c53d3e765f55e90596bd1c558c3f1686`:
lines 1--37 read, including full `b:bimodule` statement; labels located
elsewhere by search. The same finite side-projective Y has W^a=k only
at -3,0 and a genuine bimodule lift for EACH NONZERO H. No full 696-line
proof reading is claimed; its true stipulated interface is used conditionally.
- T/consequences.tex, blob `e53a2a697b2ee612a74e5ff9bc3a6ecb377c45ce`:
retrieved and authenticated 305 lines, not read. No deduction depends on
its body. Consequence statements were read in the introduction only.

## Companion and alternative screens

- AR/01-introduction.tex, blob `b053a60493956e883646a8c02c4aa2a426ba8827`:
full 268 lines read, especially `thm:main` and the two-twist construction.
It has eight split simples over K, a nonprojective Gorenstein-projective
Z, Ext^{>0}(Z,Z)=Ext^{>0}(Z,Lambda)=0, and persistence under extensions
of K. It adds no finite-field descent. AR/01-stable.tex, blob
`ca1d721a5aade7d7a8617ad367517f5dec6fd84a`, full 67 lines read.
- AR/02-conversion.tex, blob `9bd42df6ebac29da6e525a5735bea7141c36c2ba`:
lines 1--100 read, covering full `conv:proposition` and the comparison
statement/proof beginning; full 308 authenticated. Side projectivity of
F and all positive comparison isomorphisms are genuine requirements.
No full proof read is claimed. AR/07-branches.tex, blob
`b1f193996f73d04735dbe02ad70ef2d380545545`, lines 1--150 read of 233,
including the finite fiber and `branch:profile`; later twist labels were
not relied upon instead of T's fully read proof.
- Q/01-introduction.tex, blob `342efd84d3e2172d78b8bce570a6760761af522c`:
lines 1--195 read of 302, including `thm:density`, `cor:all-degrees`,
and full `cor:separable-products`. The latter ALREADY covers fixed
simultaneous polynomial values with shared factors and joint local
admissibility. Q/02-sieve.tex, blob
`db8b78ca822605cdb6dce2c12a0c48f0f4c1f157`, lines 1--110 read of 278,
including `prop:sieve-transfer`, content normalization, finite-prime and
intermediate-prime bounds. This source is screening only.
- E/introduction.tex, blob `d4bcfc0d1edd609b8c803ffa0f95b9dc68ceff2e`:
full 172 lines read. `thm:main` gives uniformly bounded vertex incidence
and F_2 coboundary expansion in every degree below d for d>=3. It imposes
vanishing of lower cohomology and uses incidence probability weights.
No universal coefficient or puncturing claim is read into it.

## External primary comparison and extent

Exact retained PDF/HTML bytes, extraction hashes, URLs and failed-version
retrievals are in `inputs/primary-records.json`. PDF conversion was local
pdftotext for reading; no third-party mathematical code was run.

- [Schulz, Finite generation of the extension algebra Ext*(M,M), 1995](https://doi.org/10.1017/S1446788700037265):
private text lines 1--115 and 230--338 read; printed pp.366--367 and
371--373, including Theorem 5 with proof and Example 7 with its syzygy
calculation. It treats bounded-module behavior and an infinite-order
quantum parameter, with nonzero first self-extension. This supplies an
antecedent distinction, not a finite-field construction or a universal
obstruction to FT2. Other theorem proofs were not read.
- [Erdmann, Ext-finite modules for weakly symmetric algebras with radical cube zero, 2017](https://doi.org/10.1017/S1446788716000331):
private text lines 25--150 read; printed pp.108--110, including full
Theorem 1.1 and preliminaries through the start of Lemma 2.1. Its
classification is for the stated weakly symmetric, indecomposable,
J^3=0!=J^2 setting over an algebraically closed field. Its parameter
restriction does not decide arbitrary symmetric algebras in FT2. No
reading of its classification proof or entire Section 4 is claimed.
- [Enomoto--Marczinzik, On the homological conjectures for Artin algebras, arXiv:2609.19172v2](https://arxiv.org/html/2609.19172v2):
web-rendered lines 24--192 and 365--404 read, including Theorem 1.1,
Proposition 3.4 and proof, and Theorem 3.5 and proof. The ambient
coefficient ring is FIXED. Their two-fold trivial extension gives a
self-injective target; this is not a field-specialization theorem or an
automatically symmetric target. Full HTML retained, not fully read.

No claim of worldwide novelty, exhaustive literature search, or current
universal open status is made. The original scope is a substantial
operation if solved. Rank specialization, trace restriction, orbit-product
invariants and finite-state periodicity are known/elementary mechanisms;
our supporting deductions using them are not contribution nominations.
