# ANS263 scoped Lean support, version 1

Myeongjin Kang; no affiliation. Original code MIT; original prose CC BY 4.0.

**Status: provisional support implementation, awaiting independent formal review. The full atomic theorem is not formalized.** The candidate's independent proof and contribution reviews are separate and unfinished. This package does not change the accepted count.

`ANS263.lean` proves 15 supporting theorems and defines six scalar/threshold objects. `Controls.lean` proves six concrete hypothesis-necessity results and defines one counterexample function. A fresh source compilation checks all 28 declaration types and reports only `propext`, `Classical.choice` and `Quot.sound`. No custom mathematical axioms, placeholder proofs or native evaluation are used. The compiler is Lean4.34.1, commit5045d0056413266e57c625dcd7c365b10e377c52; mathlib is pinned at d13f23b723b8a846827a245b89c10fc7d3f11612, with the dependency lock retained.

## Coverage and limits

| Candidate interface | Formal support | What remains outside Lean |
|---|---|---|
| Adaptive exponents in (3), (7)–(13) | Exact rational values; selected simultaneous positive margins; α>6/7 implies positive dyadic gain | Derivation of the probability bound, kernel estimates and spatial-net loss; the conjunction is not claimed to list every elementary margin in the manuscript |
| Weighted annular sum (12)–(13) | Finite geometric bound; one- and two-term weighted budgets; dyadic ratio; arbitrary-depth convergence with two independently vanishing amplitudes | Identification of actual conditional error masses and proof of their pointwise majorants; reversal/reindexing of the physical outward dyadic list |
| Physical rescaling | `scaled_annular_identity` proves s³ D^β (s x)^(7β−3)=(D s⁷)^β x^(7β−3), for s>0,D≥0,x≥0 | Quantum definitions of s,D and the nuclear initial-error estimate |
| Neutral exterior tail (14) | Scalar inequality 1/2≤1−r/d for d≥2r>0, and its finite positive-weight sum | Newton's spherical identity, measure/integral passage, field bounds and tightness |
| Radius extraction | `threshold_bracket` bounds the actual infimum of {r≥0:mass(r)≤1} between two radii, under antitonicity and strict lower/weak upper mass tests | Density integrability, convergence at the two radii and the final asymptotic squeeze |

The variable-depth theorems allow an arbitrary `depth : ℕ → ℕ`; no growth rate or bound on the number of scales is assumed. The two-rate theorem assumes independent convergence of both scalar sequences to zero. Its explicit scalar majorant remains a hypothesis: it is not an encoding of the full quantum conclusion as an assumption. The generic scalar `vanishing_budget` includes q<1, so its denominator is positive in every declared use.

The controls prove failure of a positive dyadic gain at α=4/5, failure with a negative amplitude, unbounded sums at ratio1, failure of the tail coefficient when2r is replaced by1.5r, and failure of the radius lower bracket without monotonicity. They are genuine mathematical counterexamples to dropped hypotheses, not malformed-code tests.

Not formalized: fermionic Hamiltonian/form domain, IMS likelihood conditioning, arbitrary-offset source inputs, conditional core/trial constructions, adaptive inverse comparison, nuclear barrier, weak PDE maxima and forgetting, profile compactness/rigidity, Newton integrals, or the full atomic asymptotic theorem. No source Lean implementation is imported. This package provides no contribution or priority certification.

## Reproduction

Read `rebuild.py` before execution. It verifies dependency revisions and tracked cleanliness, checks the compiler identity, copies only current Lean sources to a fresh temporary directory, compiles the support and controls, and checks every declaration's full type and kernel dependencies. Existing support object files are not used. Dependency object caches are reused read-only, and are explicitly part of the trusted build environment.

From the repository root, use a **new output directory outside this frozen package**:

```
python3 -B frontier/campaigns/2026-10-14/ans263-formal-v1/rebuild.py --output /absolute/path/to/new-output
```

For a copied package supply `--cache /absolute/path/to/formal/.lake/packages` and, if necessary, `--lean /absolute/path/to/lean`. No network fetch or dependency build occurs. The checked output is retained at `validation/sealed-build/`. Earlier development and validation directories intentionally retain failed elaboration attempts, one unused-variable warning, and successful intermediate versions; they are not the final validation record.

The external manifest anchor must come from the parent handoff. `verify.py --anchor HASH` checks exact package identity; it does not compile or prove mathematics. A fresh rebuild is a separate operation. The candidate and scope anchors are recorded in `coverage.json`. Parent authorship and implementation are not independent review.
