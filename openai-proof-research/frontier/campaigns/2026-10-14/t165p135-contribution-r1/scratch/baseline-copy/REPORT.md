# REPORT r135 (outside packet)

Provenance: Factory Droid / claude-opus-5-5 / high. Authorized mathematical discovery, round r135,
2026-10-20. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true. No self-gates, no
correctness/contribution verdict, no count, no priority claim.

Status: FROZEN_AUTHOR_PROOF_NOMINEE (full scope, frozen before proof drafting).

Claim (packet/public/frozen-statement.md, SHA-256
1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d): for all positive integers m, n,
every even-adjacent (weakly semisimple) drawing of K_{m,n} has at least d_m d_n oddly crossing
unordered edge pairs, d_r = floor(r/2) floor((r-1)/2); the balanced-axis drawing gives exactness;
consequently the weakly-semisimple odd, semisimple odd, and semisimple pair crossing numbers of
K_{m,n} all equal d_m d_n and hence (quoting the pinned thm:main) coincide with cr(K_{m,n}).

Proof: packet/public/proof.md (SHA-256 a12854336cc118cc9a49dd96bb72aeb142e618ab3466a2e1dc648ff77bf98f10).
Self-contained characteristic-2 transport of the pinned Zarankiewicz machinery: mod-2 chord
formula; parity intersection matrix with cycle pairing via a one-sided shift and exact diagonal
bookkeeping; additive block relation; subspace bound and rank-sum corollary over infinite
characteristic-2 fields; barycentric detector in characteristic 2 with the row-flip onto the
two-triangle pattern; odd-n assembly; even-n vertex deletion; axis-drawing exactness.

Strongest reduction / unpaid operation: the claim does not follow from the pinned statement
(upper bound only) nor from the real-signed proof (signed sums over-count odd pairs); the general
comparison cr <= 2 iocr^2 gives only a square-root lower bound. The paid operation is the
characteristic-2 transport itself (one-sided shift + diagonal bookkeeping, even-adjacent
hypothesis as the diagonal-block condition, field transfer, detector row-flip). The Harborth
K_{2,m,n} direction was developed prefreeze to a quantified obstruction and abandoned unfrozen.

Not claimed: unrestricted ocr/iocr/pcr of K_{m,n}; any Harborth tripartite formula; novelty as a
worldwide priority; any acceptance/count. Novelty accounting (scoped "not found" statements,
search limits disclosed): packet/public/reading-limits.md; packet/public/report.md.

Validation: artifact checks only (packet/public/sanity.py, all (a)-(h) passed; read-only verifier
packet/public/verify.py; copied-controls in artifact-controls.json). Independent adversarial
correctness review has NOT occurred; downstream stages unopened.

Read limits: packet/public/reading-limits.md. Late prefreeze reads disclosed there (arXiv
2610.25204 abstract; Schaefer DS21 excerpts; history greps; r134 seal templates). Isolation
disclosures (harness /tmp terminal logs; grep hit lists naming excluded active rounds without
content access; python3 -B throughout): packet/public/working-notes.md.

Packet MANIFEST SHA-256: 6b997e3d8605220fc4845528d8213356c792e7d674eab50d7be9d16d4730eae5
Public report SHA-256: a6d9001618c1bb150188dde4bde2e0be0e4bed3783b43e6ad41ecae5b7dec961
Verifier: python3 -B packet/public/verify.py --root <this root> --project <openai-proof-research>
  --finalhash <contents of FINAL.sha256>
