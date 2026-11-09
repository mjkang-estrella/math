# Strict new-discovery screening, 2026-10-26

Current strict-discovery count from this lane: **0**. No existing formalization, known counterexample, small-index wording failure, or bounded search is counted as new mathematics.

## Source screening

Fetched current complete MathDB records for 371791, 373100, and 374660–374666 through the public API, saved under `sources/`. Read the actual primary manuscripts arXiv:2605.10512v1 and arXiv:2512.03188v1 before computations.

- **373100 excluded:** current MathDB post contains Shivam Patel's complete prior proof of the Golombic/Levine degree formulas (reply 76b121ad-2456-411b-9d8c-2fed858a4555). No new outcome claimed.
- **374661, 374664, 374666 excluded as known:** Chen–Ono–Zhang, *Reciprocals of Partition Polynomials*, arXiv:2605.21718v1, already proves the ordinary and binary coprimality/nondivisibility conjectures and supplies existing Lean artifacts. Empty MathDB replies did not establish novelty.
- **374665 n=4 log-concavity failure rejected as known:** source-definition computation independently produced coefficients `(4,10,18,18,20,18,18,10,4)` and the interior failure `18²<18·20`. A direct four-partition calculation confirmed it. Targeted literature search then found exactly this counterexample in Chen–Ono–Zhang, Section 1.2.2, published May 2026. The later original-paper revision/publication changes the log-concavity range to n≥6. This rediscovery is explicitly not counted and no Lean proof was drafted for it.

Relevant primary links:

- https://arxiv.org/html/2605.10512v1
- https://arxiv.org/html/2605.10512v2
- https://arxiv.org/html/2605.21718v1
- https://arxiv.org/html/2512.03188v1

## Exact computational searches

Scripts use local python-flint 0.9.0 for exact integer polynomial arithmetic; installed dependencies are confined to this lane's `.pydeps/`.

1. **Binary numerator:** implemented primary Theorem 4.7 plus its even/odd equality. Checked all indices through 1024 for unimodality, log-concavity, and divisibility by the relevant `1+x^(2^i)` factors. Odd numerators equal the preceding even one. The only log-concavity failure found was the already known n=4 (and hence n=5) exception; no new n≥6 failure or unimodality failure appeared. The coprimality checks are not a claim to improve the already known theorem.
2. **Ordinary numerator:** computed the actual common-denominator numerator through exact partition-generating-function dynamic programming with the primary denominator formula. Every polynomial division was checked exact. Proper nonconstant factorization over Q, denominator gcd, and unimodality of the **compressed even coefficient subsequence** were checked for 2≤n≤75. No new factor or shape failure was found. Scalar content is ignored when screening intended irreducibility; inserted zeros in an even polynomial's coefficient array are not used as a wording counterexample.
3. **Ordinary denominator 374663:** exact incremental denominator formula checked through n=500. Log-concavity failed only at the four source-listed exceptions n=3,5,6,7; no new failure appeared.
4. **Falling factorial 371791:** exact full factorization of `x(x−1)…(x−k+1)−a!` checked for all 5≤a≤200 and 2≤k≤min(30,a−3), then for all a through 700 with k≤min(100,a−3). Only the stated exceptions `(k,a)=(3,6),(4,7),(20,23)` occurred in these ranges. The larger scan was interrupted at the parent's request to switch to proof review; no claim beyond fully completed a=700 is made. Degree one cannot be a proper factorization. No known exception is counted as new.

Completed search result summaries are `search-binary-result.json`, `search-ordinary-result.json`, and `den-result.json`. `falling-result.json` records the completed smaller scan; the interrupted larger scan has no falsely completed result receipt.

## Paused screening for an independently reviewed proof candidate

The parent requested pausing brute-force screening for a mathematical review of its prospective universal normed-triangle 3/2 inequality. The detailed adversarial review is `taxicab-independent-math-review.md`. The argument was found mathematically valid after correcting a harmless missing factor 1/3 in one cross-product expansion. A standalone formal source geometry bridge was then built in `formal/TaxicabGeometry.lean` at the parent's request.

This bridge is **supporting work**, not a new counted discovery or a complete scalar/geometric outcome by itself. Prior-art review remains separate; the cited 2018 normed-space Erdős–Mordell literature may subsume the result. No manuscript or formalization was started on a claimed new polynomial result, because none passed the novelty gate.
