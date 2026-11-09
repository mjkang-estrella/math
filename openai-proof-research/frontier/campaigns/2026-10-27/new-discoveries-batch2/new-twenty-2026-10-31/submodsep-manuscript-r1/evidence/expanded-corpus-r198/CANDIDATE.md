# MathDB 341850: submodular separation is impossible at (r,d) = (2,5)

Status: strong candidate, zero accepted credit. The mathematical certificate is exact. The general Lean negation and semantic bridges compile strictly; source-version, novelty and independent-review gates remain separate.

The primary target is Brakensiek–Gopi–Guruswami, arXiv:1902.04740v1, Conjecture 3.33, page 23. It asks for a polynomial-time evaluable integer-valued submodular function negative on the low-degree monomial image and nonnegative elsewhere. The claim below refutes even existence without the evaluation-time condition. The actual SIAM journal PDF returned 403; that host was not retried. The authors' current publication page points to arXiv and ECCC, both obtained. The journal's exact final conjecture remains unread.

## Exact ordinary proof

There are five Boolean input variables. Label the fifteen nonconstant output coordinates by the five singletons, then the ten pairs in lexicographic order. Interpret a mask m between 0 and 32767 as a subset of these coordinates. Add the empty-monomial coordinate, always equal to 1. Thus this is exactly a face of the source's sixteen-coordinate Boolean lattice. For X contained in {0,1,2,3,4}, write q(X) for the mask containing the singletons and pairs contained in X. The good family is precisely {q(X): X subset of [5]}.

Suppose f were a separator. Restrict f to this face and average over S5. Use the sum, rather than division, so that g(m) = sum over all 120 permutations sigma of f(sigma m). Coordinate permutations preserve unions, intersections and the good family. Consequently g is submodular, g(m) <= -120 on good masks, and g(m) >= 0 on bad masks. Moreover g is constant on permutation orbits.

The nine submodular rows in outputs/submod-dual-compressed.json have terms (meet,+1), (join,+1), (left,-1), (right,-1) and positive weights. Each row therefore has value <= 0 for g. Add four sign rows: -4g(3), 5g(615), 2g(5871), and -3g(16383). Masks 615 and 5871 are good; 3 and 16383 are bad. The sum of all thirteen weighted rows has coefficient zero on every orbit. Its upper bound is -120(5+2) = -840. Hence 0 <= -840, a contradiction.

No source formula evaluation is involved: the search establishes impossibility of any submodular function with the prescribed signs. The source does not provide a separator or this obstruction.

## Exact verification and reproducibility

The initial full-face LPs were feasible at (d,r)=(2,2),(3,2),(3,3),(4,2). A symmetric-orbit LP was infeasible at (5,2); (4,3) reached its solver time limit, not an infeasibility conclusion. A dual certificate with 310 rows was recovered by exact Fraction elimination. Adding general submodular rows compressed it to thirteen rows with integer weights and denominator 7.

Run python3 -I scripts/limited.py verify-new python3 -I scripts/verify_compressed.py from this lane. Use a fresh log name. This independently expands the thirteen rows under all 120 permutations, directly verifies the meet/join relations and all signs, and checks every integer coefficient cancels. Its existing receipt and full output are logs/compressed-verification.* and outputs/certificate-verification-compressed.json.

## Credit risks

The journal body is unread due access denial. The current GitHub search and Lean Pool screen located no matching prior proof in their bounded scopes; that is not global novelty clearance. The Omega recursive tree is truncated, so no complete Omega clearance is asserted. A general known characterization of submodular sign families might subsume the certificate; that needs independent review. The finite obstruction and source semantic bridge need literal Lean replay. No acceptance or campaign count change is claimed.

## Lean result

Separation.source_existence_refuted : ¬ Separation.SeparationExistence is proved in lean/Certificate.lean. The existence assertion quantifies over every dimension and degree and demands the full submodular sign-separation property. The stronger bare-existence assertion is refuted; the added polynomial-time-evaluation requirement cannot restore existence. The fixed finite obstruction is used inside this general negation. The coordinate model includes the empty monomial and every low-degree subset label.

The group-averaging argument, its preservation of signs, and all coordinate-renaming identities are proved in lean/Separator.lean. The finite equality and bad-family tests use kernel decide. There are no axioms, sorry, admit, unsafe, native_decide or ofReduceBool in the sources. The transitive report on the final theorem lists only propext, Classical.choice and Quot.sound. A fresh extracted strict rebuild passed; the initial checker attempt failed because lean was absent from PATH, so a separate explicit Certificate checker invocation uses the full binary directory.

Final packet verification: logs/lean-final-verified.receipt.json records return code 0, peak sampled group RSS about 2.52 GB, and 21 seconds wall time. All 45 local declarations, including generated declarations, passed the allowed-axiom audit. Fresh strict rebuild and explicit Certificate leanchecker both passed. Lean packet: lean-packet.zip.
