# Higher-chaos-moment attempt at temporal nonconstancy

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Supporting calculation; full target unresolved.

Write F-EF=sum_(k>=1) F_k in orthogonal Gaussian Hermite chaoses, w_k=E F_k². For the finite positive measure

    mu_n = n^(-1/3) sum_k w_k delta_(k n^(-2/3)),

Cov(Z_n(0),Z_n(t))=integral exp(-|t|lambda) dmu_n. Its total mass tends to a2>0. Its first moment is n^(-1) E||grad F||² <= beta²(n-1)/(2n). Thus mu_n are tight on [0,infinity). This controls mass escaping infinity, but neither excludes a limit a2 delta_0 nor ensures uniform integrability of lambda. Positive first moments can be carried by vanishing mass at diverging locations.

The natural next attempt is a uniform second moment. The exact Hermite derivative identities give

    integral lambda² dmu_n = n^(-5/3) E[||Hess F||_HS²+||grad F||²].

Let s(sigma)=(sigma_i sigma_j)_(i<j), M=n(n-1)/2. Then

    Hess F = (beta²/n) Cov_Gibbs(s).

Since this covariance is positive semidefinite and trace<=M, its Hilbert--Schmidt norm squared is at most M². The resulting bound is only

    integral lambda² dmu_n <= (beta⁴/4)n^(1/3)(1-1/n)²
                                      +(beta²/2)n^(-2/3)(1-1/n).

It diverges. Bounded spins alone do not pay the needed uniform integrability.

There is a more informative exact form. Draw four conditionally independent Gibbs replicas at the SAME disorder. Put R_ab=n^(-1)sum_i sigma_i^a sigma_i^b. Since s(sigma)·s(tau)=(n²R²-n)/2, expansion of the squared covariance yields

    ||Hess F||_HS² = (beta⁴ n²/4)
          <R_12^4 - 2 R_12² R_13² + R_12² R_34²>.

This is exact at each disorder, not an asymptotic claim. The constant and linear overlap terms cancel by conditional replica symmetry. A sufficient second-moment route would need the annealed bracket to be O(n^(-1/3)), which is not a conclusion of the scalar moment theorem, its chaos consequence, or the read comparison interfaces. No such bound is asserted here.

For logical comparison only, measures

    a2 delta_(2 n^(-2/3)) + c n^(-1/3) delta_(n^(1/3))

have total mass tending to a2, positive first-moment limit c and second moment of order n^(1/3), while weakly tending to a2 delta_0. They also respect the absence of degree-one chaos by using degree2 and degree n. This is NOT an SK counterexample. It shows that the available numerical orders in these spectral estimates alone permit a frozen limiting covariance. In particular a lower bound on the SK gradient energy would not by itself finish the target.

The full-sequence mixed-law problem remains unpaid even if temporal nonconstancy were separately established.
