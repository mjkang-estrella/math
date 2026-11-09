# Lane: pi-discrete-r1 (batch 2, discrete) — progress

Date: 2026-10-27. Solo Pi worker, no children, no provider switches, no shared edits.

## Target selection

Primary target: **MathDB 372432 = BBK Conjecture 5.1** (arXiv:2601.04014 §5):
`G_{k,n}(q) := (q^{2k-1}; q²)_n/(q; q²)_{n+1} ⪰ 0` for all k ∈ ℕ, n ∈ ℕ₀.
Equivalently (verified below) for k ≥ 2:
  G_{k,n}(q) = (q^{2n+3}; q²)_{k-2} / (q; q²)_{k-1},
and G_{1,n} = 1/(1-q^{2n+1}).
Strong lead carried from pi-discrete-discovery-r7 (FINDINGS §5): exact eventual-
periodicity structure, all poles simple, two remaining gaps (uniform tail
positivity; initial-segment positivity). Uncounted; no proof there.

Backup targets: 374706 (q-Fibonomial unimodality), 357859 (Clar covering
unimodality) — screen if 372432 stalls.

## Novelty / freshness screen (done first)

- MathDB 372432 record (saved m372432.json, r7 lane): open, 0 solutions/comments.
- Semantic Scholar citations of arXiv:2601.04014 (live fetch 2026-10-27):
  exactly 5 citing papers: 2609.05961, 2606.30208, 2604.05403, 2601.19845, 2410.14190.
  - 2601.19845 Chern–Wang: proves F_{k,1} ⪰ 0 for ALL k (published Discrete Math.
    2026, DOI 10.1016/j.disc.2026.115409) — does NOT prove the G_{k,n} refinement
    (r7 lane read full text: no G_{k,n} positivity).
  - 2604.05403: congruences for the limiting sequence; abstract-level answer-mode
    read 2026-10-27: no G_{k,n} positivity content.
  - 2606.30208: two-color companions S_1/T_o/T_e; no G_{k,n} content.
  - 2609.05961: mock-theta denominator microscope; no G_{k,n} content.
  - 2410.14190: congruences (2024, predates).
- MathDB record references 2306.09450 and 1312.7548 as also "stating" the
  conjecture: checked 2026-10-27. 2306.09450 is a commutative-algebra Hilbert
  depth paper (stale/mis-linked record reference). 1312.7548 (Guo) is binomial
  divisibility + q-analogue generalizing q-Catalan positivity — not G_{k,n}.
- Conclusion: Conjecture 5.1 is a fresh, open, well-posed exact source question.

## Work log

1. Read BBK §5 primary text (r7 cache bbk-2601.04014.txt lines 850–980):
   Conjecture 5.1, (5.1), (5.2), Lemma 5.3, Conjecture 5.4 verified verbatim.
2. Citation screen as above.
3. [next] Study Chern–Wang technique; exact recomputation of structure; attack
   the two gaps.

## Honesty notes

- No counting claim until: complete uniform proof of both gaps + Lean + novelty.
- Access limits: Semantic Scholar 429 on first call (retried OK); no paywalled
  bodies (Discrete Math 2026 paper read via arXiv version).
