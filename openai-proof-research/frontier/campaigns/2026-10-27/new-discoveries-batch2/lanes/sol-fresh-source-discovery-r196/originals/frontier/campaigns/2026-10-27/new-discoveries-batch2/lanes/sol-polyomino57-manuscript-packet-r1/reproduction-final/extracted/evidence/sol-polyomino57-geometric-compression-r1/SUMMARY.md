# Same-candidate helper: complete geometric finite-certificate compression

**Complete alternative computer-assisted coverage obtained; no ordinary all-cases proof or Lean claim.** The literal fixed-orientation, holes-allowed universal 11-cell containment statement is unchanged. Credit 0; campaign 5/30 additional, 35 total. Existing exhaustive proof remains valid.

Use discovery.md for the rigorous reduction and lower-bound certificate argument; verify_certificate.py is the independent checker. Required payload files are exactly certificate-files.json. The checker does not use the original animal list, import the generator, or trust a solver result.

Signed-diagonal extrema reduce all possible counterexamples to 70 parity/span domains. Thirty-five have an immediate empty collision group. Four more are eliminated by 596 small forced-cell superset checks. For the remaining 31, certified group-Steiner potentials prove every connected set meeting all hole-collision and boundary-extrema groups has at least 12 cells. Checking base, edge and disjoint-merge inequalities proves this lower bound by an elementary rooted-tree induction.

Final payload: 1,874,144 raw bytes / 238,227 gzip bytes, versus original 10,880,385 / 475,654 bytes. Ratios are **5.806× raw, 1.997× equally compressed**. The 1932.4× reduction from animal cases to 70 domains is a structural comparison, not a scalar-entry or runtime ratio. Full proof coverage comes from the exact extrema/group reduction, not from matching enumeration counts. The new tables have more scalar entries than the original has animal rows.

Replay:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 180 python verify_certificate.py

Hard AS 512 MiB, CPU 160/165 seconds, alarm 175 seconds. Successful independent replay is saved in verification.json and verify-run.log; generation is separate. No animal family regeneration, network, children, git operations, other-lane edits or formal-worker reads/writes.

A checked exact-size-11, exact-radius-4 counterexample to the five-shift heuristic is given in discovery.md and verification.json. The missing shift (1,−1) is its unique good center. Thus a closed ordinary argument still cannot rely on that heuristic. The initial C++/Node attempts failed under the stated environment/resource constraints; final work uses Python/NumPy. These failures and the initially larger compressed prototype are recorded candidly.

Helpful formal interface: prove the three finite potential inequalities imply a connected-set cardinality lower bound, then prove the signed-diagonal normalization and collision-group reduction. This is an optional alternative, not an instruction to replace or duplicate the active full formalization. No PROOF.md is created because the result still relies on finite certificate checks.
