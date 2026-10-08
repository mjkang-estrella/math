Raw Claude review — not endorsed without root corrections. Task node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h022-lazy-eds-cost-review-opus-20261008-r1

I'm reviewing the lazy-prefix EDS cost claim against the Liao–Zhang source text and the H019/H021 screens. Read-only: no edits, runs, child agents or experiments.

**Verdict: the lazy-prefix ledger is accepted. The stated constants are right as an upper bound for this one implementation, with small corrections. Improvement: NONE. No experiment is justified.** The extra robustness check (the "floor" in §4) makes the rejection stronger.

## 1. Dependencies and normalization (accepted)

**Point function.** By Lauter–Stange Theorem 2 as quoted in the source, ϕ is a function of the point on ⟨G⟩. It is odd: q−1 is even, q−1+N is odd and N is odd, so ϕ(−P) = −ϕ(P). Here q and N are the source's names for the field size and group order. In our notation the condition gcd(q, p−1) = 1 holds automatically for full-range, prime-order ordinary curves except tiny cases.

**Known keys.** h_i = ϕ(iG)/ϕ(G), with h₁ = 1. Odd terms use h_{2l+1} = C_l D_{l+1} − C_{l+1} D_l, costing 2M. Even terms use eq. (15), costing 2M plus a multiply by the precomputed h₂⁻¹, so 3M. Generating h_i needs support C, D only up to index ⌊i/2⌋+1. Building D_{l+1} needs h_{l+2}, which already exists once l > 2. With h₀…h₅ bootstrapped from eq. (6), no term is ever used before it is computed.
- Arithmetic: 2.5M per key, plus 0.5(M+S) per key for its own half-prefix support.
- **cg = 3 + 0.5s ✓**

**Why one initial scaling is enough.** Write B = DG and w_x = ϕ(xB)/ϕ(B). The Ward relation is not invariant under scaling every term by a constant: the left side has degree 2 and the right side degree 4. The target recurrence works anyway because only the dynamic terms are scaled. The support C^B and D^B stays in w-normalization (g₁ = 1), so each side picks up γ².
- Target terms are t = γw, with γ = ϕ(B)/ϕ(G).
- The recurrence is t_{child} · t_{anchor} = t_{m+1} t_{m−1} C^B_n − D^B_n t_m².
- So a single initial scale, ϕ(·)/ϕ(G), is correct. In practice you can just bootstrap ϕ(Q−jB)/ϕ(G) directly.
- This step is what removes the source's 1M-per-giant-key rescaling (its Algorithm 1 cost of 4M + 0.5S).

**Target recurrence.** Let x = k′ − j. Taking m = k′−l with n = l gives child j = 2l with anchor t_{k′}. Taking n = l+1 gives child j = 2l+1 with anchor t_{k′+1}, i.e. j = −1. Both children use parents j = l−1, l, l+1.
- Eq. (18) prints "h2ℓ+1"; this is a pdftotext artifact for h²_{ℓ+1} = C_{l+1}, not a typo in the paper.
- **Bootstrap correction:** you must bootstrap j ∈ {−1, 0, 1, 2}. The pair from l = 1 needs j = 2 as its own parent, so it is circular. After that, every l ≥ 2 uses parents up to l+1 ≤ 2l−1, which already exist.

**Target cost.** Shared parent work is P = t t (1M) and Q = t² (1S). Each child then costs 2M plus 1M for the anchor-inverse multiply. Total: 7M + S per pair, i.e. 3.5M + 0.5S per key.
- Support for B is needed up to J/2 + 2. Each support index costs 2.5M to generate g_n (its own support at n/2 is the same C^B, D^B, so nothing is double-counted), plus 1M + 1S for C^B and D^B. That is 3.5M + S per index, or 1.75M + 0.5S per target key.
- **cb = 5.25 + s ✓**

## 2. Coverage and stopping cost (accepted)

- A match ϕ(Q−jB) = ±h_i gives Q − jB = ±iG, so k = jD ± i. The sign of the key equality picks which candidate (h_i ≠ 0 and the characteristic is odd).
- After rescaling to the unit square, the stopping cost is a·u + b·v with ab = cg·cb·q/2. At every cost level, the diagonal growth path maximizes the covered area uv, so it is optimal pointwise and not merely among symmetric schedules.
- Choose D ≈ √(2·cb·q/cg). Grow the two prefixes at a ratio of cb/cg known keys per target key (≈1.75 at s = 0).
- The expected cost is then (2√2/3)·√(cg·cb·q) under a uniform prior. The worst case is √2·√(cg·cb·q).
- Edge rounding, wrap-around, granularity and overshoot add O(1) keys.

## 3. Charges kept separate (lower order unless noted)

- **Bootstrap:** about 6 ϕ evaluations — ϕ(G), ϕ(DG), ϕ(Q), ϕ(Q+B), ϕ(Q−B), ϕ(Q−2B) — each O(log p) field operations including the 1/N² power. Also O(1) inversions: h₂, g₂, ϕ(G), and the two anchors. Plus one scalar multiplication to get DG.
- **Zero exceptions:**
  - Q = O makes the anchor t_{k′} zero → return 0.
  - Q = −DG makes t_{k′+1} zero → return q − D.
  - A zero t_j (Q = jB) is a key-0 sentinel; the recurrence tolerates zero parents because it only divides by the anchors.
  - h_n and g_n are never zero for 0 < n < q.
- **Lookups:** one insert and one lookup per key, as in the baseline. A canonical sign representative costs no multiplications. Do not square keys to remove the sign; that would cost an extra S per key.
- **Non-injective keys:** each table entry must keep every index with that key, and every candidate must be checked by scalar multiplication.
  - The expected number of false checks is O(1) only under a heuristic that ϕ behaves randomly (the source reports 1.18 matches on average). No deterministic bound follows.
  - The x-only baseline has no false matches at all, since x(P) determines P up to sign. This is a qualitative point against EDS, not a cost-model item.
- **Memory (correction, in EDS's favour):** support C and D can be consumed as a stream (each index is used by two adjacent children), so it needs only O(1) storage. What must be kept are sliding parent windows of about I/2 known values, J/2 target values and J/4 g values, plus the key tables. That is still more than the baseline's (x, index) records.
- **Fine print:** for j ∈ {0, 1728} curves, the extra automorphisms must be matched on both sides; that case is out of scope.

## 4. The count is one implementation, not a lower bound

| Variant | Effect |
|---|---|
| Multi-anchor children (generalizing Remark 3: 2r bootstrapped anchors, children at 2l+a) | target children cost → 3M + (M+S)/2r, so cb → 4.75 + 0.5s. The product (3+0.5s)(4.75+0.5s) still exceeds (2.5+s)² by 8 − 1.125s − 0.75s² ≥ 6.1 |
| Storing even known keys in parity scale (keys × h₂) | saves 0.5M per known key but costs 1M per target key; the product moves by about −0.1, no gain |
| Making the target anchor equal 1 by rescaling | moves 1M per key onto the known side; worse |
| Swapping strides (paper layout with a once-scaled target) | exactly symmetric, same constants |
| Reusing target support from known keys | not possible: g_n = h_{nD}/h_D lies far outside the known prefix |
| **Floor:** every anchor multiply free, numerators at 2M, half-prefix support kept | (2.5+0.5s)(3.5+0.5s) beats the baseline only for s > 0.927, by at most 1.0% in the square root at s = 1. No construction achieves this floor, so it is not a candidate |

## 5. Comparison and scope

The claimed gap stands: cg·cb − (2.5+s)² = 9.5 + 0.625s − 0.5s², which is positive on [0, 1]. As ratios of the leading coefficients, EDS is about 59% worse at s = 0, 37% worse at s = 0.8 (4.535 vs 3.3) and 34% worse at s = 1.

The baseline's batch-inversion overhead does not change this for any reasonable batch size. This is a single-target arithmetic screen in the limit with bounded I/M; field additions are omitted.

It does **not** establish:
- wall-clock behaviour;
- a lower bound for every EDS method, including ones using tripling or elliptic nets;
- anything about multi-target amortization;
- anything about the rolling Ward schedule, which Astra is reviewing.

**Disposition:** reject the lazy contiguous prefix as a gain candidate. Improvement: NONE.
