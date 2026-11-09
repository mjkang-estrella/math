# Proof structure

Growth proves F n≥(3/2)^n/2 by simultaneous induction on adjacent Fibonacci numbers and F n≤2^n by two-step induction. It applies the pinned polynomial/geometric ratio limit with degree23, base3/2 and tolerance1/768. For n≥1, n≤n^20, so eventually F n/(192n^3)≥n^20+n. This is an explicit application, not an asymptotic hypothesis.

The actual finite bad-mark bound is at most exp(n^20-N/(192n^3)): 2^M≤exp(M), 1-p/2≤exp(-p/2), and floor(N/6)≥N/12 for N≥12. The rational blockLower is converted exactly to the real 1/(8n^3). Thus its bound is exp(-n) for every N≥F n eventually.

For n≥2, L=2n^20/(2n+1)≥n^18 and sqrt(L)≥n^9. The concentration remainder is bounded by 4/n^18+2(3n^6+2)/n^9 =4/n^18+6/n^3+4/n^9. Uniform instantiates actual_finite_interval_tail at n^20 and width3n^6 with all rational/natural/integer casts checked. Each inverse-power term tends to zero by inverse-at-infinity; exp(-n)≤1/(n+1) gives its zero limit by squeezing.

For q=n^5, the unchanged actual suffixTailMass_bound and 1-p≤exp(-p) give (3N+1)exp(-n^2/8). Fibonacci upper growth and 2≤exp(1), 4≤exp(2) give 3N+1≤exp(n+3). For n≥32, n+3-n^2/8≤-n. For n≥8, 3n^5+n+3≤n^6, yielding literal inclusion of the STRICT event n^6<T-lastSplit in the inherited suffixTailDomain. Pointwise nonnegative actual masses complete the result. No conditioning at lastSplit is introduced.
