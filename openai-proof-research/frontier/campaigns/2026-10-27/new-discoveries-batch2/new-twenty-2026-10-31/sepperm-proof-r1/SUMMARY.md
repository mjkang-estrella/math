# Handback: MathDB 362890

**Not accepted and not fully formalized. Root decides.** No counterexample was found. No full independent proof is claimed.

The useful advance over r129 is an explicit all-index Newton transform: for every k >= 3, the actual full-class decline U_k-U_(k+1) equals

    t^k(1+q) sum_(j=0)^(k-3) binom(k-3,j) G_j(q),

where G_j are EXACTLY the kernels in the public Omega theorem `RecordNewtonPositivity.actual_q_record_newton_nonnegative`. The ordinary derivation uses the actual record quadratic, its normalized Motzkin coefficient formula and Pascal's identity. It does not assume polynomial coefficient positivity. See ATTEMPTS.md for the full derivation and the precise supplier dependence.

This gives a conditional full proof using that public sign theorem. The imported theorem has not been rebuilt with its dependencies in this lane. The complete actual-permutation Lean bridge is also missing. If the public sign theorem is accepted as a supplier, the result may be a short corollary of substantial existing public work; significance and subsumption need root's review before further investment.

Two portions have independent all-n ordinary proofs here: the strict rise from one to two records, and the strict first decline from two to three. They use the scalar Schröder recurrence, an eventual ratio bound, finite initial values, and an exact rational-function identity. The latter identity has an independent symbolic polynomial-ring certificate, not just finite numerical testing.

The corrected computations reproduce all rows through n=250 and independently enumerate classical pattern avoiders through n=7. The Newton identity was checked as an exact polynomial identity through k=42; composition signs were checked for kernels 0 through 39 through degree 250. These checks support the derivation but do not prove its unbounded sign premise. The original real-rootedness route fails at n=4. The first exploratory Motzkin normalization was incorrect, caught at n=3, corrected, and retained as an explicitly obsolete attempt.

`formal/Partial.lean` compiles against Lean 4.34.1 and the pinned read-only mathlib cache. It defines the literal avoidance Finsets of permutations, all four statistics, and `LiteralEndpoint`; proves the local Newton pairing identity and two scalar polynomial positivity certificates; and reports only permitted axioms. There is no theorem `mathdb_362890`. Replay with `bash scripts/replay.sh`. The successful measured replay used 2.39 s wall time and 1,739,760 KiB maximum RSS; logs/lean-07.log and logs/lean-07.resources.log retain the replay and axiom reports.

Live source checks found only arXiv v1. The author manuscript still states Conjecture 1. Current pinned Omega HEAD is e4b00585d5883d418860e7fa253bb76eb04f8da7, dated 2026-11-03T10:49:37Z. Its dossier still distinguishes the irreducible peak-three problem and the kernel theorem from the missing actual-record bridge. Receipts and hashes are retained. Bounded searches did not identify a full published proof/refutation; the journal version-of-record body, complete citation corpus and global novelty remain unverified.

Deliverables: ATTEMPTS.md (ordinary arguments and exact remaining Props), results.json, formal/Partial.lean and Partial.olean, scripts, full logs, public-source receipts, exact rows, and SHA256.json. All writes stayed inside this lane; r129 was read-only. No agents, git, shared-ledger mutations, uploads, messages, browser tabs, denied-route retries or lingering background jobs were used.
