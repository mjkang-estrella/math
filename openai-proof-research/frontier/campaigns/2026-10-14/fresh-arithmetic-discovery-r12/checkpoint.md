# OA057 review handoff

Status: COMPLETE_AUTHOR_PROOF_PENDING_INDEPENDENT_PROOF_AND_CONTRIBUTION_REVIEW. Not accepted, counted, formalized, committed, or published.

The fixed original theorem in scope.json is proved in candidate.md at its full all-dimension/arbitrary-finite-order/SNC scope. The sole stipulated nonclassical input is the manifold abelianity theorem at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Scope selection preceded the final proof and reviews. No target narrowing occurred; only explicit edge-case and attribution clarifications were added. Dimension zero and empty boundary reduce to the input. Curves retain possibly disconnected auxiliary divisors.

Main proof interfaces for adversarial review: (1) exact-M permutation/translation action and repeated-coordinate detector; (2) full local Kummer normalization at mixed SNC intersections; (3) actual stabilizers have zero boundary coefficients, allowing root-line descent before resolution; (4) proper lifting of fixed-point local sections gives auxiliary divisorial submersions; (5) all differential poles excluded by these lifts; (6) exceptional meridians map to products of individually divisible local meridians. The candidate explains each, without assuming residual finiteness, scalar quotient singularities, or global uniformization.

The closest source already pays the order-two pairwise affine idea, specialness transfer, descent facts and group endpoint. reading-and-comparison.md contains the actual operation comparison and precise reading limits, including general finite-flat stack realization and residual-finiteness-based group realization. Whether the remaining compatible all-order construction is substantial remains an independent decision. Author correctness and contribution claims are not review verdicts.

Run `python3 -B affine_checks.py` for exact finite diagnostics: 31 moduli through32, 34317 group-law checks, 496 equal-power translation checks, 62 fixed generators, 9801 mixed-inertia checks; two false stronger claims are refuted as negative controls. Output must equal affine-checks.json. These checks do not prove universal algebra or geometry. The elementary action formulas are proved universally in candidate.md.

Formal feasibility is restricted to supporting finite algebra/cardinality interfaces described in scope.json. No Lean file or full formalization is claimed. Root stacks, resolution, specialness and full-group topology remain mathematical proof obligations for independent human/model review.

Reproducibility: invoke `python3 -B verify_inventory.py --manifest-sha256 EXTERNAL_HASH`, using the hash supplied outside the packet in the handoff. The verifier is offline and read-only, checks the exact regular-file and directory inventory, rejects links, checks file hashes and lengths, validates saved input receipts, and reruns diagnostics. Wrong-anchor testing must fail before reading inventory content. No hash proves mathematics or novelty.

Rights: original candidate, comparison and code are authored for Myeongjin Kang (no affiliation), CC BY4.0 for prose and MIT for original code. Files under private/ are reference/context snapshots retaining their original rights, not covered by these licenses and not cleared for public redistribution. No private snapshot is a proposed public upload. Sources are not rewritten or relicensed.
