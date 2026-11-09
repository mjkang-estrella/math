import T088P133
open T088P133
theorem strict_interface : (∀ (α β p q d P N : ℝ), 0 < α → 0 < β → α+β=2 →
    0 < p → p < 1 → q=1-p → 0 ≤ d → 0 < P → 0 < N →
    2*d*p^2 < P → 2*d*q^2 ≤ N →
    (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) < 1) := @rational_mixture_lt_one
