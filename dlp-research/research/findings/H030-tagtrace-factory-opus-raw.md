# H030 tag-tracing prior-art/cost review — raw, not accepted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h030-odd-selector-tagtrace-review-factory-opus-20261008-r1`
Provider/model: acpRegistry_factory_droid / claude-opus-5-5
Completed 2026-10-08. Root reconciliation pending; exceptions are not presumed rare, and illustrative costs are not universal bounds.

# H030 review: prior art and full-work skepticism for the h-sign selector in tag tracing

## Verdict

**High-risk partial candidate, kept on paper only. No code should be admitted yet.**

- **The algebra holds.** Using h to pick the sign does remove the specific obstacle Bos names: the negation map needing y while tag tracing skips y.
- **Most of the √2 does not come back as a net gain.** The repair restores the negation quotient, so the comparison becomes "tag tracing vs. a competent negation walk". There, the best this saves is Bos's own y-omission ceiling, at most 6/5 per step as τ grows.
- **Charged costs shrink or reverse that margin.** These are a signed table (more entries, wider entries), the cycle handling small r brings, extra canonicalization and table latency. At realistic (r, τ) the margin looks like a few percent and may be negative.
- **Scope.** This is a constant-factor kernel candidate only. There is no exponent change and no whole-work claim.

## Sources actually read this session

- **Bos et al. 112-bit paper, §3.4.** I read it from `/tmp/h029lit.4NEx/bk.pdf` with pdftotext, because the bk.txt column layout was garbled. It says:
  - Skipping y saves `(τ−1)/τ·(2A+M)` per step, giving "approximately 6/5 at best (large τ)".
  - Table retrieval cost grows with τ, so τ stays moderate in practice. Rarely used entries can be pruned.
  - Tag tracing "is incompatible with the negation map, because the latter needs the y-coordinate", which costs a factor of about (5/6)√2.
  - The only exception they allow is the case where r must be small and doubling should be avoided. Then tag tracing without negation might give a small speedup.
  - Table 2 slowdown factors are (r+1)/r for look-ahead f and (r+4)/r for g. The caption says most entries are lower bounds.
- **Bernstein–Lange–Schwabe, PKC 2011** (cr.yp.to/elliptic/negation-20110102.pdf), targeted passages:
  - The walk is f(W) = |W| + R_h(|W|), with fruitless 2-cycles at probability about 1/(2r).
  - With batched inversion, a step costs 5M+1S.
  - On Cell they canonicalize **y** once and use it for the sign, the table index and distinguished points (DPs). They use r = 2048 (a 64 KB table).
  - Canonicalization costs 24.75 instructions against 43.75 per multiplication. These are their Cell figures, not a general rate.
- **Project records (not reopened as primary sources):** H027 Rück attribution for the local coefficient, H028 Liao–Zhang and GWZ, and H019/H020 records of Bos thesis §4.6.

**What I could not read:** ePrint 2011/461 (Zhang–Wang point halving, binary fields) and ePrint 2013/644 (Bos–Costello–Miele) both returned 403. I did not open the Cheon–Hong–Kim original.

**Searches with no result:** six bounded searches on elliptic-curve tag tracing combined with negation, and on odd selectors that avoid y. None found a primary source combining tag tracing with negation over a prime field, or using a Miller/cocycle sign. This is not evidence of novelty.

**Unread recall:** in characteristic 2, λ-coordinates give a cheap sign bit. I have not read a source for this, and it is outside the scope here anyway.

## Algebra check: it holds

- **Sign update.** Let the representative be W = ε(P0+K), with ε making εH canonical. Then the next class is the class of P0 + K + εJ_i, and the label is ε·(label(P0) + label(K)). This matches the candidate's update `nextK ← K + εJ`.
- **Refresh.** At refresh, h(P0′) = εH exactly, so h does not drift.
- **Exceptions.** K = 0, tangency (K = P0), K = −P0 and h = 0 (which falls back to a paid y) are all rare. Each needs an explicit branch.
- **h is the only selector of this kind.** Any F_p-valued f with f(P+Q) = f(P) + f(Q) − λ differs from h by a homomorphism Z/q → F_p. That homomorphism is 0 because q ≠ p. So any slope-updated odd selector found in other work would be this h under another name.
- **Rational odd selectors cost a y.** Every rational odd function has the form y·g(x), so it needs y-equivalent work. h is non-rational. It is cheap only because it is carried as state: 2A per step, plus one more field element per table entry and per trace origin. This explains why the selector works. It is not a theorem about every possible selector.

## Cost skepticism

### 1. Signed table growth

Over a trace, K ranges over all nonzero integer vectors with L1 norm at most τ. That count is `Σ_k 2^k·C(r,k)·C(τ,k) − 1`. Storing ± pairs once, with the sign applied on load, halves it. Each signed entry also stores (x, y, h), 1.5 times the width of Bos's (x, y).

| r | τ | Bos unsigned | Signed | Signed, folded ± |
|---|---|---|---|---|
| 16 | 2 | 152 | 544 | 272 |
| 16 | 3 | 968 | 6016 | 3008 |
| 16 | 4 | 4844 | 50048 | 25024 |
| 2048 | 2 | 2,100,224 | 8,392,704 | 4,196,352 |

When r is much larger than τ, the folded ratio tends to 2^(τ−1), and bytes grow by a further 1.5 times. Per-step index ranking of the signed vector is integer work that also has to be charged.

### 2. The real tension is not repaired

- Negation wants large r to suppress fruitless cycles (BLS uses 2048 with no look-ahead).
- Tag tracing wants a small table.
- At r = 2048, τ = 2 needs about 4.2M entries of three field elements each, far outside fast memory.
- At r = 16, the look-ahead slowdown is about 17/16 (a Table 2 lower bound), and 16-adding costs about 1.016 more steps with negation (accepted H029 Table 1 figure).

h does nothing for this tradeoff.

### 3. Per-partial-step arithmetic ledger

- **Baseline (BLS):** 5M + S + 6A + one canonicalization.
- **Candidate:** 4M + S + 6A + canonicalize H. It must also canonicalize x for the hash, unless field elements are already fully reduced, because BLS hashes from the canonical y it no longer has.
- **Rough net under weighted S = M:**
  - Ceiling: 6/(5 + 1/τ), which is 1.09, 1.125 and 1.14 at τ = 2, 3, 4.
  - With BLS-like lazy reduction, the extra canonicalization costs about 0.5M per step.
  - With the r = 16 overheads above (look-ahead and the 16-adding penalty) added, the estimate goes **negative**.

These figures are illustrative, not measured.

### 4. Walk law

The h-rule picks different class representatives, so it is a **different deterministic class map** from the y-rule walk. No rho collision constant or Bos Table 1 ratio transfers to it. Fruitless-cycle rates and the collision law are heuristic only.

Note that τ does not change the walk itself. Tag tracing only changes how the same h-rule walk is computed, so the walk-law question can be tested separately from the cost question.

### 5. Setup, replay and labels

- The table can use multiples of G only, which makes it per-curve, but single-target accounting still pays for it once.
- That setup is about S/2 additions plus a Miller bootstrap for h(G) and h(Q).
- It is negligible at cryptographic sizes but biased against synthetic fixtures. For example, 3008 entries is roughly 10% of the step count near q ≈ 2^30.
- Seed replay and labels in the style of Bos and BLS are already known. Using them here is no gain by itself.

## Unreviewed amendment for root

The next partial step needs only λ, not x(P0+K). If the partition index and the DP predicate use canonical |H|, and x is computed and stored only at DPs (x stays the collision key), each partial step also skips S + 2A and the x canonicalization. The per-step ceiling then rises toward 1.5.

The table and cycle tension is unchanged. This uses h as a partition function, which sits closer to H028's territory. No one has checked it.

## Cheapest falsifier

**Paper first, no code.** Fix the field size, a fast-memory budget in bytes, the operation weights, the canonicalization policy and the cycle-handling policy. Then write the exact per-logical-step ledger for the h-rule tag-traced walk at every (r, τ) whose folded signed table fits the budget, and compare it with a BLS-style baseline at that baseline's own preferred r.

**Kill condition:** no (r, τ) gives a positive margin after look-ahead or escape cost, the r-adding penalty, the extra canonicalization and index ranking.

**Only if it survives:** run one small synthetic curve at a single fixed (r, τ). Check:
- class-by-class equality between the tag-traced walk and a full-point h-walk;
- the fruitless 2-cycle entry rate and the sign-flip rate, compared with the y-rule walk using the same jumps and partition.

This test cannot establish a speedup.

No edits, experiments or child tasks were made. Network reads went to stdout only.
