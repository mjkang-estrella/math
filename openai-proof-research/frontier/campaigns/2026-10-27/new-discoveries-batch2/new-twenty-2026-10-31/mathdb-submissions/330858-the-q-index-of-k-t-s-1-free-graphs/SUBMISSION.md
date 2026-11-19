# MathDB 330858: The Q-index of K_{t,s+1}-free graphs

- Problem: https://mathdb.com/p/330858
- Source: MathDB330858; de Freitas, Nikiforov, Patuzzi, arXiv 1507.00625v1, Conjecture 4
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `QIdx.qindex_kts_endpoint`, `QIdx.qIndex_isGreatest`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `q-index-kts.pdf`, `q-index-kts.roff`
- Lean source: `qindex-330858-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded source-primary investigation, not worldwide priority certification. prior_limits: No citation index. A UFRGS thesis, Indices de grafos livres de K_{s,t}, lume.ufrgs.br/handle/10183/180762, could not be retrieved after a connection reset and is known by title only; if it proves Conjecture 4 this acceptance must be withdrawn. The LAA 496 final version of the source, the body of Yu, Wang and Guo, ELA 30 (2015) 795-811, and RAIRO Operations Research 10.1051/ro/2023109 (HTTP 403, title never seen) are unread. The 2026 papers arXiv 2606.30272 and 2609.21367 were read and do not prove or imply the conjecture. An SBMAC proceedings item surfaced by the audit was read by root and is unrelated. Registry roots closed. trust_limits: Upstream Lean, mathlib and their oleans are trusted through pins and were not rebuilt; the auditor verified the hashes of Mathlib.lean and lake-manifest.json and root verified the mathlib revision. Reviewers are AI systems, not human referees, and the reviewers, auditor and Lean author share a model family; the audit read the proof and the earlier reviews first, so it is verification and not independent invention. The two written proofs share one mechanism. Conjecture 4 was compared by the audit through the text layer; one qualification viewed the glyphs of the page. not_claimed: Worldwide novelty or publication priority; Human peer review; The unrestricted reading of the equality clause; Any explicit or optimal threshold beyond the stated thresholdN
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: for all s, t with t >= 2 and t-1 <= s there is N(s,t) such that every K_(t,s+1)-free graph on n >= N vertices has Q-index, the largest eigenvalue of A+D, at most n/2 + s + t - 2 + (1/2)sqrt((n-2+2s)^2 - 8s(n-2) + 4(t-1)(n-t+1)), with equality exactly for the join of K_(t-1) and an s-regular graph on n-t+1 vertices, assessed within the freeness hypothesis as in the source. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For all naturals s, t with 2 <= t and t-1 <= s there is N depending only on s and t such that for every n >= N and every simple graph G on Fin n that is K_{t,s+1}-free in the ordinary non-induced sense, the largest element of the real spectrum of A + D is at most the printed bound n/2 + s + t - 2 + (1/2) sqrt((n-2+2s)^2 - 8s(n-2) + 4(t-1)(n-t+1)), and among such G equality holds exactly when G is isomorphic to the join of K_{t-1} and an s-regular graph on n-t+1 vertices. The equality clause is inside the freeness hypothesis, as in the source.

## Body (paste into the MathDB body field)

Use the written proof in this folder: q-index-kts.pdf. The complete Lean source is in qindex-330858-source-only.zip.
