# I251 — reading extent and failed attacks

2026-10-12. Independent mathematical proof gate only; no significance gate and no acceptance/count change. The requested candidate hash was verified before review.

## Read in full

- AGENTS.md and sources/upstream.json.
- frontier/iterations/iteration247-quantitative-complete-rigidity-brief.md.
- frontier/iterations/i247-quantitative-complete-rigidity.md.
- frontier/experiments/i247_quantitative_complete_rigidity/analytic-attempt.md, including early notes, complete positive-deficit proof, all counterexamples and excluded geometry bridge.
- The same I247 directory's reading-and-failures.md and input-authentication.json.
- frontier/sources/i247_quantitative_complete_rigidity/literature.md.
- frontier/findings/R016-complete-crouzeix-equality.md.
- frontier/experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md.
- frontier/experiments/i245_crouzeix_rigidity_proof/analytic-check.md.
- I247 direct-primary-excerpts.tex.txt: tensor convention and main theorem statement; the entire retained Sections 2–3 including proofs; outer-approximation lemma statement. This fully read text was copied into the assigned I251 source directory.
- The direct source's actual lem:approx and its entire proof, freshly retrieved at the pinned raw URL. The full excerpt was read before retaining a copy.

## Bounded reads and provenance only

Read sources/CONTENTS.md lines 7925–7955 for problem 325 and the direct/structural companion descriptions. An initial filename inventory was broader than needed and displayed many AGENTS/upstream filenames; it read no contents of those files or live review artifacts. Subsequent reads were explicit approved paths only.

Fetched the 35,174-byte direct pinned manuscript in memory for SHA256/Git-blob verification and verbatim comparison of three retained blocks; did not read or retain its other sections. Machine lookup in sources/preprints-tree.json selected only its exact main.tex entry; the complete tree was hashed for provenance, not read as manuscript text. The extracted raw Git blob agrees with that entry. No whole-repository history, snapshots or live siblings were read.

R016/I242/I245 were finished permitted background and their statements of previous success were not accepted as evidence that this positive-deficit candidate passes. I reconstructed its residual and checked its new algebra separately. No I246 material was needed for a correctness-only verdict. No I243, I248, I249, I250 or other current review was read. Structural companion full text, Jin, ACV and MathDB were not newly read: their results are not inputs to Q1–Q4 or this proof verdict. The I247 literature record was read for context, without adopting it as independent source validation.

## Attacks and their resolutions

- Looked for a missing factor two in the residual: source cross constant is four, subtracting the a² constant leaves three, and the residual doubles it to six; candidate correct.
- Looked for an invalid positive-deficit equality limit: use the same pair and gamma/M_j, pass upper bounds by strong L²; no equality-only inference occurs.
- Tried failure through nonnormality or eigenvalue collisions: determinant bound with algebraic multiplicity, not delta^(-1), controls the resolvent.
- Tried a hidden lower bound on conformal speed: weighting by |q|² and using arclength supplies the claimed constant; no such bound is assumed.
- Checked singular congruence minmax with a one-dimensional kernel: the (d-1)th singular value, not the smallest singular value, is bounded.
- Checked interlacing at d=2, zero a2, and approximate instead of exact range orthogonality: all covered by the stated minmax argument.
- Checked complex tensor conjugations and both linear error terms: base-first X0=xi u^T gives p=v*P u, and both terms cancel exactly by maximal-pair stationarity.
- Checked active-block local normalization M_B<1 and multiple full-A active blocks: the local residual only improves; the extension properly claims existence, not full-A every-pair recovery.
- Independently computed Crabb support blocks, the shifted-disk Gram matrix and entangled tails, the weighted output chain, and independent unused coefficients. No numerical experiment or scan was used.
- An intermediate review sentence overstated the counterexample deficit range for all t<=1/2; it was corrected before finalization. The candidate only needs t tending to zero and contains no such overstatement. One may restrict to t<=1/4. This is not a repair to the candidate.

## Operations

Early partial review notes were written before completing the source check. Only permitted I251 review, analysis, reading, source and authentication files were written. Utility Python performed text editing, bounded source extraction and provenance hashing only. No research implementation, tests, numerical computation/scans, agents, communications tools, shared-state changes, staging, commits or publication. Final verdict: PASS for Q1–Q4 and its stated extension; quantitative disk geometry remains outside the proved result.
