# T298P leading-score normalization clarification

This parent clarification records an exposition typo in the independent proof review. It changes no frozen author or review bytes and opens no new proof claim.

In t298p-proof-r2/review.md, section6, the displayed leading score is
Xi_j^0 = (epsilon k^2)^(-1) sum_a V_aj tensor xi_a.
The next equality there omits the scalar prefactor in its displayed energy. With the pair basis normalized by
sum_j tr_k(V_aj V_bj) = delta_ab,
the product trace gives, without orthogonality assumptions on the xi_a,

sum_j ||Xi_j^0||_2^2
= (epsilon^2 k^4)^(-1) sum_(a,b) [sum_j tr_k(V_aj V_bj)] tau(xi_a^* xi_b)
= Phi*(U)/(epsilon^2 k^4).

The xi_a are the conjugate variables of the self-adjoint tuple U. The finite column Gram identity removes cross terms. In particular this computation does not assume the individual conjugates are mutually orthogonal.

This is the factor already present in the original candidate's equation(3) and t298p-formal-r1/T298P.lean leading_score_energy. The latter is a conditional finite real Hilbert-space identity: it does not establish the specific matrix Gram identity, identify conjugate variables, justify the analytic Neumann series, or prove the full Fisher bound.

Under t = epsilon^2 k^2 u, integrating the leading Fisher term with dt gives the factor k^(-2) in the entropy increment. The manuscript author was notified to retain both factors explicitly. This note is elementary parent corroboration of the stated interfaces, not an independent analytic proof gate, new result or count credit.
