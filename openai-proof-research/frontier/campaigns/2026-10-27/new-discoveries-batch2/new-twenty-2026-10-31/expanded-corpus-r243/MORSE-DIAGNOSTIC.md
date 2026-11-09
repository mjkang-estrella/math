# Ineligible source-formula diagnostic: 343470

No discovery credit or Lean formalization is requested for this calculation. It is an evaluation of the source's own model and Theorem 4.2 truncation algorithm, which the task explicitly excludes from credit.

The source is Gao and Gu, arXiv:1908.03914v1, Section 4.2 and Conjecture 4.13. It identifies the Morse link number L_n with the weighted Catalan number whose up-step from height h has weight (2h+1)^2 and whose down-steps have weight 1. The conjecture's literal repeating 5-adic integer is

alpha = 10 + 25(1 + 5 + 5^2 + ...) = 10 - 25/4 = 15/4.

For n = 785, 4n - 15 = 3125 = 5^5, so the printed odd-index formula predicts valuation 8.

The exact weighted-path recursion starts D_0(0)=1 and updates

D_(t+1)(h+1) += (2h+1)^2 D_t(h),
D_(t+1)(h-1) += D_t(h) for h > 0.

Thus L_785 = D_1570(0). The unbounded-integer computation gives

L_785 mod 5^10 = 7,812,500 = 4 * 5^9,

so its valuation is 9. A second computation restricts heights to 0 through 17. Any omitted path reaches height 18 and includes an up-step from each height 0 through 17. The product of these weights has valuation 10: the odd integers 1 through 35 include 5,15,25,35, with valuations 1,1,2,1, and the weights are their squares. Therefore omitted paths vanish modulo 5^10. This is exactly the product-divisibility principle in the source's Theorem 4.2. The truncated transfer returns the same residue.

The scan checks 4 <= n <= 3000 modulo 5^15 and finds this one discrepancy in that range. It does not determine a corrected infinite 5-adic formula, resolve any adjacent conjecture, or prove global novelty. The independent integer check and transfer check are recorded in logs/morse-verified.txt. The initial independent run failed only while formatting an unnecessarily large integer's decimal digit count; that failure and the corrected bit-length output are both retained.

Reproduce from this lane with:

    python3 -I -B scripts/cap.py morse python3 -I -B scripts/search_morse.py
    python3 -I -B scripts/cap.py morse python3 -I -B scripts/verify_morse_final.py

The computational checks are ordinary exact arithmetic, not kernel-certified Lean theorems.
