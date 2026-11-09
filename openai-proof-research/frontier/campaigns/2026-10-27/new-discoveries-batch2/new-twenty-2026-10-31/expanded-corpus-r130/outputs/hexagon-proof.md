# 346745: full ordinary bridge, proposed routine exclusion (root decides)

Write F_s for the nonnegative hypergeometric series in source Conjecture 1, and H_s for its bilateral series. Source equations (2), (4), and Gauss's identity give H_s = Theta F_s, where Theta=1+2 sum_{j>=1}(-1)^j q^{2j²}. This identity is also checked exactly through q^4096 in the retained diagnostic.

All four series satisfy (1-q²)F_s >= 0 coefficientwise. For s=2,4, their n=0 summand gives (1-q²)/(1-q)=1+q; in each n>=1 summand the factor (1-q²) cancels a denominator factor and everything remaining has nonnegative coefficients. For s=3 the same argument applies. For s=1, separate n=0 and n=1: their contribution after multiplying by (1-q²) is 1-q²+q²/(1-q)=1+q³/(1-q). For n>=2 cancellation again proves positivity.

Consequently (1-q^{2d})F_s=(1+q²+...+q^{2d-2})(1-q²)F_s >=0 for all d>=1. Put a=k+1+2h. Pair the alternating tail consecutively to obtain

(-1)^k (Theta_k F_s-H_s)
= 2 sum_{h>=0} q^{2a²}(1-q^{4a+2})F_s >=0.

All sums are locally finite coefficientwise. This proves all four signs for every positive integer k. The bridge consists entirely of the source's own exact product identities and consecutive pairing of an alternating tail. Under the task's explicit exclusion of routine bridges, recommend exclusion rather than new discovery credit. No Lean endpoint or novelty claim is supplied. This is not merely a numerical non-finding.
