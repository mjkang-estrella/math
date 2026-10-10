# Separate clarifications — original bytes unchanged

These clarify the comparisons already present in R154. They are not a repaired theorem or a substitute for completion of the independent review.

1. In the capped fallback, the safe explicit bound is
   `TV(noisy capped output, pi_V) <= e^(-4) + 2 L_d c`.
   The first term is the exact capped sampler's failure bound; the second compares the actual stateful noisy sampler to it. An accepted noisy proposal need not have law pi_V. No new algorithm, hypothesis, cap, or tolerance order is needed for this reading of the original proof.
2. The replacement process in (7)–(8) retains the actual conditional next-state kernel. Its visible transition is the exact compiler marginal, but its stored transcript is not an exact-oracle transcript. The original explicitly makes this distinction. Enlarged-state KL closeness is to this synthetic process only.
3. The older unrestricted internal-reserve independence claim stays FAIL. Restricting independence to standalone top-call final reserves is already explicit in R154; it does not retroactively repair the old sentence.

No substantive correction of equations (1)–(19) is asserted by this incomplete review. No PASS is issued by incorporating these clarifications.
