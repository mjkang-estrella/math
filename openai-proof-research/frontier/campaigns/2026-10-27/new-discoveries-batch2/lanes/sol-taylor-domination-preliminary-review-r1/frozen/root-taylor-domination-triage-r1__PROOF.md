# Ordinary resolution of the literal Taylor-domination question

Status: complete mathematical refutation; novelty and substantive eligibility **HOLD**, not accepted. No Lean or manuscript claim.

Primary source: Friedland–Goldman–Yomdin, *Exponential Taylor domination*, [1909.04918v1](https://arxiv.org/pdf/1909.04918v1), Definition 1.1 p2, Definition 2.1 p5, and Section 4 example 2 p9. The question asks whether every function with (p,1,C k^p)-Taylor domination is K(C)p-valent in the open disc D_(1/2), for a constant depending only on C. Its quantifiers require one K(C) to work for every positive integer p and every analytic function satisfying the stated coefficient bound. It does not require f to be a Borel transform or itself p-valent. Those extra hypotheses belong to the separate Theorem 3.1.

We refute this with C=1, even when a_0 is excluded from the initial maximum, and even with all witnessed zeros simple. Fix any integer t>=1, set p=3^t and m=pt, and put

    f_t(z)=z(1+(3z)^m)=z+3^m z^(m+1).

This polynomial is entire. Since m+1>p, its first p+1 coefficients have maximum absolute value 1; the maximum over indices 1 through p is also 1. For every integer k>=p+1 all coefficients vanish except at k=m+1. At that index,

    |a_(m+1)|=3^m=3^(pt)=(3^t)^p=p^p<=(m+1)^p.

Consequently the literal (p,1,k^p)-Taylor domination holds at every required index.

Besides z=0, the roots are

    z_j=(1/3) exp((2j+1) pi i/m),  j=0,...,m-1.

They are distinct, nonzero, and have modulus 1/3<1/2. They are simple because the derivative of 1+(3z)^m is nonzero there; the root at zero is simple since f_t'(0)=1. Thus the equation f_t(z)=0 has m+1 distinct solutions in D_(1/2). For any proposed finite K=K(1), choose an integer t>K. Then m+1=pt+1>Kp, contradicting Kp-valency. This proves the negation of the full uniform assertion, not just a fixed-p violation. The exact integer checks in exact-checks.json are diagnostics only; the argument above covers all t.

Second independent mechanism, with distinct **real** roots: for t>=1 let p=5^t, m=pt, c_j=3+j/(m+1) for j=1,...,m and

    g_t(z)=product_(j=1)^m (1-c_j z).

The roots 1/c_j are distinct and lie in (1/4,1/3), inside D_(1/2). Write g_t=sum b_k z^k. Because all c_j>0, its alternating coefficients satisfy

    sum |b_k|=product (1+c_j)<5^m=p^p.

For k>p, therefore |b_k|<p^p<=k^p max_(0<=i<=p)|b_i|, since b_0=1. The maximum excluding b_0 is also at least 1 because |b_1|=sum c_j>1. The number of distinct zero preimages is m=pt, with unbounded m/p. This independently establishes the same refutation without root multiplicity or a zero constant coefficient.

Both constructions also obey the weaker tail bound k^(2p-1), so the same obstruction applies to the universal suggestion in Remark 2.4. That is the same family, with no second credit. Neither construction refutes Theorem 3.1: p here is a domination cutoff, not a claimed valency of the starting function.

Closest known proofs read: source Theorem 2.3 and Remark 2.4; Batenkov–Yomdin 1301.6033v2 Theorem 2.3; 1411.7629v1 Theorem 2.2; Friedland–Yomdin 1503.00325v1 Theorem 2.1; Roytwarf–Yomdin 1997 Lemma 2.2.3 and Theorem 2.3.2. These give upper bounds depending on the whole sequence or a smaller radius. None of the inspected statements provides a linear bound at fixed radius, or explicitly states the above lower construction. Their existence is not proof of novelty: lower-bound examples elsewhere, and direct classical subsumption, remain to be checked. Elementary size alone is not treated as an exclusion, but root should specifically assess whether this is an already known generic sharpness example.
