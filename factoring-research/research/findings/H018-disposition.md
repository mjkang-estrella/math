# H018 coordinator disposition

2026-10-08. **Accept the analytic model comparison and conditional deductions
after independent review and two local corrections. Verified full factoring
complexity improvement: NONE.**

The [corrected derivation](H018-degree-envelope.md) and
[independent review](H018-independent-review.md) establish the fixed-r
coefficient-line construction at (H^(r-1)+S_all) poly(n), its upper population
bound, and the exact optimum of the explicitly conditional relaxation:

    c_*³ = 64(r-1)[(r+1)+(r-1)eta]/(9r²).

Here r>=2 is fixed independently of input size, while d and scalar widths
may grow polynomially in bit_length(N). Increasing r worsens this particular
optimistic relaxation. That comparison is not an actual useful-yield comparison
and the upper population bound is not a lower supply theorem.

The exact r=2, eta=4/5 witness a=1, b=19/20, delta=7/5 gives optimistic
envelope 1.90. Its line polynomial, coefficient interval and integer cutoff
are accepted as mathematical constructions, without implementation or run.
The stronger homogeneity-based lattice count is explicitly unproved; only
its consequence for the same model is accepted. Fixed-degree volume
intuition cannot absorb degree-dependent factors such as d^(C*d).

The parent applied both requested local statement fixes:

1. The exact 1.90 comparison uses 93193/26000, whose squared numerator is
   8684935249. The prior 93203 comparison was true but not equivalent.
2. Homogeneity describes the unfloored real threshold. Floor and unfloored
   thresholds select the same integer vectors, not the same real set.

The originally reviewed bytes are preserved in
[H018-submitted-draft.md](H018-submitted-draft.md), SHA-256
072060c6b244e526199b416de797b2336a3c220b9ab548adec382a770fb0cfe8.
Of 13 manifest file checks, 12 current files matched; the sole changed report
matches that immutable snapshot exactly. The corrected current report has
SHA-256 c45526bb5df1ff1676609d419861c07163a510a7c62f2049ea8847db480cfb00.
No new finite experiment or Lean theorem was added.

The next substantive question is an actual discrete linear-tail supply
bound with degree-uniform geometry and N-only certificates, assigned to
[H020](../hypotheses/H020.md). A finite or conditional scarcity result must
not be promoted to an all-input factoring lower bound. A constructive route
must still pay for supply, smoothness, rank and complete factor extraction.
