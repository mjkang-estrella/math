# H012 LD8 independent Opus review (raw)

Provider claudeAgent, model claude-opus-5-5; completed, no pending children.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h012-ld8-work-review-opus-20261008-r1`.
Reviewer worked from the frozen prompt, not workspace files. Root corrections
and accepted scope are in H012-adaptive-operation-screens.md. In particular,
Wald applies to intrinsic seed/descent costs, not all history-dependent costs.

# LD8-v1 review: the frozen operation is Ω(√(q log q))

**Verdict:** I found no errors that change the result. The proposed rejection holds for the operation as you froze it. For every instance Q (including d = 0), the expected number of group additions until a verified d is found satisfies

  **E[X] ≥ (3/32)·√(q·(2⌈log₂q⌉ − 7))**, which is Ω(√(q log q)).

Without the popcount refinement the bound is E[X] ≥ (3√3/32)·√q, which is Ω(√q). Three statements need small fixes before the card is written; they are listed under "Points to fix" below. I worked from the prompt only and did not read any workspace files.

## Independent proof

**1. The endpoint map.** The descent rule uses only the current point, the eight neighbours P + kG, and the keys. So the endpoint map F: E → E depends only on G and the key function. It does not depend on Q, a, b, A or B.
- **Wording to fix:** "F independent of Q/labels" should read "F depends on G and the keys; it is independent of Q and of the (A, B) bookkeeping." F does depend on the point keys.
- **Ties:** distinct points have distinct keys, and O = (−1, 0) is below every affine key. So "strict descent to the minimum" is well defined, and any step that sees O moves there and stops.
- **Distinct moves:** the step set {±1, ±2, ±4, ±8} is distinct and nonzero mod q for every prime q ≥ 17. All pairwise differences are at most 16, so a collision would need q to be one of 2, 3, 5, 7, 11, 13. The condition q > 17 is therefore stronger than needed.

**2. Start distribution.** R = aG + bQ = (a + bd)G. The map (a, b) ↦ (a + bd, b) is a bijection of Z_q², so R is uniform and independent of b for every d, including d = 0. B never changes during descent, so the endpoint's B equals b. Each trial's endpoint F(R) and its B are therefore independent, and trials are i.i.d.

**3. When the algorithm can succeed.** Trials i and j can collide usefully only if F(R_i) = F(R_j), which has probability Σ_H (b_H/q)² = κ for each pair. A collision with equal B forces A₁ = A₂ and gives nothing. An O endpoint with B = 0 forces A = 0 and gives nothing. A collision with different B, or an O endpoint with B ≠ 0, always gives the correct d, because B₂ − B₁ is invertible in a group of prime order. So verification never fails, and the only success routes are the two you named. By a union bound, P(T ≤ n) ≤ nπ_O + C(n,2)κ, where π_O ≤ √κ follows from κ ≥ π_O².

**4. Expected number of trials.** Write s = √κ and take n = ⌊1/(2s)⌋.
- Then P(T ≤ n) ≤ ns + n²s²/2 ≤ 5/8, so P(T > n) ≥ 3/8.
- E[T] ≥ Σ_{m=0}^{n} P(T > m) ≥ (n+1)·3/8 ≥ **3/(16s)**.
- This holds for every κ, including s > 1/2 where n = 0, because then 3/(16s) < 3/8 ≤ 1.

**5. Descent length.** After ℓ moves the start is H − jG with |j| ≤ 8ℓ. So at most min(q, 16ℓ + 1) points of basin H have path length ≤ ℓ; wrap-around mod q only shrinks this count.
- Sort the basin by path length, 0-indexed. The m-th point has ℓ_m ≥ ⌈m/16⌉ ≥ m/16.
- Summing gives Σℓ ≥ b_H(b_H − 1)/32.
- Using Σb_H = q and Σb_H² = q²κ: **E[ℓ] ≥ (qκ − 1)/32**. The arithmetic and rounding in your argument are correct.

**6. Cost per trial, in group additions.** Each evaluation of a non-O point costs 8 additions.
- A trial that ends at a non-O minimum does ℓ + 1 evaluations, because the last one certifies the minimum.
- A trial that ends at O does ℓ evaluations, and a trial that starts at O does none.
- So descent costs at least 8ℓ additions, giving E[descent] ≥ (qκ − 1)/4. Leaving out the certification evaluation, rejection-sampling bits, table operations and verification only makes the bound more conservative.

**7. Seed cost.** Since q is an odd prime, 2^(n−1) < q < 2^n with n = ⌈log₂q⌉.
- P(a < 2^(n−1)) = 2^(n−1)/q > 1/2. Conditioned on that event, a is uniform on n − 1 bits.
- So E[popcount(a)] > (n − 1)/4, and the same holds for b.
- Selected-bit addition costs at least popcount(a) + popcount(b) − 1 additions. This holds with a single accumulator, and also with two accumulators plus one final combining addition.
- So **E[seed] ≥ (n − 3)/2**, which is at least 1 for q ≥ 19.

**8. Wald's identity.** Trial costs c_i are i.i.d. and nonnegative, since each is a function of that trial's (a_i, b_i) and rejection bits only. The event {T ≥ i} depends only on trials 1 to i − 1. Wald's identity therefore gives E[X] = E[c]·E[T]. This is valid even though c_i is correlated with whether trial i triggers success, and even if E[T] is infinite. In fact T is finite almost surely, because each pair of trials succeeds with probability κ(1 − 1/q) > 0.

**9. Combining.** E[c] ≥ L + qκ/4 with L = (2n − 7)/4 > 0 for n ≥ 5.

  E[X] ≥ (3/16)·(L/s + qs/4) ≥ (3/16)·√(Lq) = (3/32)·√(q(2n − 7)),

by AM-GM, since the minimum over all s > 0 is taken. Without step 7, using only E[seed] ≥ 1, the same calculation gives E[X] ≥ (3√3/32)·√q.

## Points to fix in the card

1. **"seed ≥ 1" is not true for every trial in addition units.** A seed with a = b = 0, or with total popcount 1, costs 0 additions. Use E[seed] ≥ (n − 3)/2 ≥ 1 for q ≥ 19, or count random bits, which are at least 2n per trial deterministically. Wald's identity only needs the expectation.
2. **"c ≥ constant·qκ"** should be stated with the −1 term handled: 1 + (qκ − 1)/4 ≥ qκ/4 per addition. With one unit per move it is 1 + (qκ − 1)/32 ≥ qκ/32. This works as long as E[seed] ≥ 1.
3. **Fix the accumulator structure in the operation text.** The bound "popcount − 1" holds for both structures described in step 7. A vaguer description such as "two skips and no combine" would weaken the seed term to (n − 5)/2, which is 0 at n = 5. That does not change the asymptotics.
4. **Early O with bad B is fine.** An O endpoint with B = 0 sits inside the π_O mass and simply counts as a non-useful trial. Counting O-pairs in both nπ_O and κ is harmless overcounting. A tighter version, nπ_O + C(n,2)(κ − π_O²)(1 − 1/q), is available but not needed.
5. **State the units.** The bound counts group additions, including exceptional cases (doubling, or a result equal to O) as one operation each. The 2n precomputation setup is excluded. Including it only adds O(log q).

## Scope

- **What it is:** a bound on expected cost for every instance Q, on every prime-order curve with q ≥ 19, for this exact frozen operation: full eight-neighbour strict descent, endpoint-only table, fresh paid uniform (a, b) on every restart, every trial run to completion.
- **What it is not:** it is not a generic lower bound over coordinates, and it does not rule out restart algorithms in general. It also does not hold with high probability, only in expectation.
- **Variants that break it:** capped descent, storing intermediate or distinguished points, seeds derived from earlier points or cheap uniform-point seeds (which remove the log q term and break independence), and adaptive restarts. Each of these needs its own analysis.
- **Status:** LD8-v1 has no verified win. The rejection above is sound for the frozen operation as stated.
