# Expanded corpus r101

**No accepted solutions; no full literal Lean endpoint.** `results.json` contains exactly the 20 reserved IDs, each with literal-statement provenance, source hashes, review depth, source-lemma checks, actual attempts and remaining gaps. Campaign counts and shared files were not changed.

The main finding is an **unaccepted ordinary counterexample candidate for 381433**. The graph of the cyclic Latin square of order 6 has 36 vertices. Distinct cells are adjacent when they share a row, column or symbol. Its least adjacency eigenvalue is −3 and its quadratic stability bound is 6. After deleting the open neighborhood of any vertex, both quantities remain unchanged. Its independence number is 5. Thus the graph appears to refute the exact adverse-implies-Q conjecture in the supplied survey. The ordinary proof, exact rational witnesses and all-vertex verification are in:

- `outputs/LATIN36-ORDINARY-PROOF.md`
- `outputs/latin36-certificate.json`
- `outputs/latin36-verified.json`
- `scripts/latin.py` and `scripts/latin_verify.py`

The proof factors A+3I as the Gram matrix of the 18 row/column/symbol incidence vectors. The quadratic objective is a sum of 18 expressions (2y−y²)/3, bounded above by 6. Rational fractional transversals supported outside each neighborhood attain 6. Nonzero incidence-kernel vectors supported there certify eigenvalue −3. The classical parity obstruction excludes a 6-transversal, and a 5-cell independent set is exhibited. All 36 deletions and all 1,296 Gram entries were checked with exact Fraction arithmetic. These are ordinary mathematical certificates, not Lean certificates.

**Qualification remains unresolved.** The cited 2001 Cardoso–Luz preprint CM01/I-17 and 2016 JCO 31(1), 311–326 bodies, and later same-object literature, have not been read here. The current survey does not discuss Latin-square graphs in the inspected body. The classical cyclic-Latin parity obstruction receives no novelty credit. Root should decide whether the adversity certificate supplies substantive new content or is a routine previously known specialization before commissioning full formalization. A full source-semantic Lean endpoint, including spectral minima, QP suprema, all deletion graphs and the independence bound, is still absent. There is no proof packet to replay and no axioms audit claim.

The source's own results dispose of two records: **342973** is refuted by its printed signed Tutte construction (Theorems 2 and 3, Corollary 1); **375034** follows immediately from its stronger Theorem 1.2. The inherited unindexed exclusion for **365404** was retained and that route stopped: `root-nearline-r1/screening.md` identifies a later Lin–Zang proof. Its later body was not independently read here.

Substantive bounded non-findings include:

- Wigner 6j sums: 194,220 pairs in a long low-k strip, plus 105,049 pairs in a wider diagonal region (overlap not deduplicated). Only the stated zero (2,3); 420 exact Sympy sign cross-checks agree. Both regions extend past the source's displayed rectangle.
- Genocchi cycle counts: exact anchored Hamilton-cycle DP through n = 11, beyond the authors' n ≤ 6; all agree, including 51,943,281,731 at n = 11.
- Cambrian intervals: all 55,920 pairs across six B3 Coxeter words; 40,000 sampled B4 pairs; 100,000 sampled B5 pairs. No violation. The source's unspecified small-type cutoff prevents a claim that B5 is new coverage relative to the authors.
- Fibonacci gaps: integer classifications through 10 million for gap lengths 1–500 and through 100 million for 11 selected lengths. Finite-prefix differences are not counterexamples to equality of infinite sets.
- Tree covers: all 90 connected triangle-free atlas graphs through order 7 and 180 seeded connected samples of orders 8–16 satisfy the bound.
- Involution bumps: 17,401 marked bumps in the alphabet-5 sweep and 392,714 in the alphabet-6 sweep through length 9; no repeated increment of a letter.
- Network decomposition: 80 four-boundary networks and 80 five-boundary networks pass the complete-ray LP model. The initial five-boundary model omitted five rays and its 31 infeasibilities are invalid diagnostics, preserved explicitly as such.
- Composite-base colored partitions: 52 exact coefficient sequences through n = 20,000; no finite computation can settle the requested unboundedness/nonregularity assertions.
- Hexagonal graphs: 98 of 100 directly colored; two hit a local node cap. This does not exceed the source's enormous grid experiments. DFJ order-20 LP optimizations timed out and provide no polyhedral conclusion.

Analytic/spectral targets received targeted primary-body dispositions, not invented finite checkers. For 373925, source Problem 9.4 explicitly requires a robust definition of “rear-central”; the narrative does not yet determine a literal asymptotic predicate. No source wording correction is credited.

Registry HEADs were fetched only through `/commits/HEAD`, at 2026-11-02 04:56 UTC: OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`; Omega `e26965e84ef74f66ce64631e23f293569195a4c1`. Complete current Omega D5 and Problems trees were retrieved (13,418 and 1,643 entries, untruncated). The related Zeitlin six-j dossier and two actual Lean bodies were read; they concern different sum identities. OpenAI's unchanged HEAD was bound to the inherited preprints listing. This is a bounded path/body screen, not complete public-proof or literature clearance. Previously denied web-search/arXiv-API/publisher routes were not retried.

All writes were confined to this lane, with no child agents, git, package installs, shared edits, browser tabs, publication or external messages. Expensive processes used the copied cap wrapper: at most two CPUs, CPU 120 seconds, wall 140 seconds and sampled RSS 6 GiB; every attempted search has a full log, with resource receipts for launched processes. Peak sampled RSS was below 2 GiB. Missing compiler/header attempts and failed cross-check harness attempts are retained; Python DP replaced the compiler route and the corrected exact cross-check passed. The pass is bounded and does not claim the several-hour exhaustive depth envisioned in TASK.txt, or any formal completion. No background process is left running.
