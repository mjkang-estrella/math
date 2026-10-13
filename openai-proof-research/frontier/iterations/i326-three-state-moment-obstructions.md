# I326 — two insufficient three-state moment constraints

2026-10-13. **Parent technical obstructions, not an accepted finding or a counterexample to tree capacity.** These exclude two tempting replacements for I319's missing positive-channel/product-preserved class. Fourteen findings remain accepted toward twenty.

For a balanced permutation-invariant three-state posterior law, use zeta=p0+omega*p1+omega^2*p2, with omega^3=1, and write m=E|zeta|^2, h=E Re(zeta^3), k4=E|zeta|^4. Combine experiments independently conditional on the common uniform spin. I319's finalized exact Bayes calculus is the input, not an unproved common-law recursion. Its report SHA256 is `6ede78bdba2c832980aa3779b2db9d27f7de58b45e56559c1a9d583cba50712b`; its analysis is `cac50980ec9010aa9ffe2b55cb40f30db1d501d2d7d681a143b3c2ac444fb3ba`.

## 1. No finite quadratic lower bound on h implies subadditivity

Let R reveal the spin, Q report a uniformly chosen different label, and U reveal nothing. The symmetric posterior laws have respectively (m,h)=(1,1),(1/4,-1/8),(0,0). For nonnegative t,u with t+u<=1, reveal an independent selector and perform R,Q,U with probabilities t,u,1-t-u. Call the resulting law M. Then

    m(M)=t+u/4,       h(M)=t-u/8.

In two independent copies, a revealing branch determines the spin. If neither branch reveals, an exclusion paired with U has information 1/4 and two exclusions have information 5/8. Therefore

    m(M*M)=2t-t^2+u(1-t-u)/2+5u^2/8,
    2m(M)-m(M*M)=t^2+tu/2-u^2/8.             (1)

For every finite C>0 choose a constant A>9C/64 and put t=u/8+A u^2. For all sufficiently small positive u, these define valid mixing weights, and

    h/m^2 = A/(3/8+A u)^2 > C,
    2m-m(M*M) = -3u^2/64+(3A/4)u^3+A^2u^4 < 0.

Thus even h>=C m^2 with arbitrarily large prescribed C cannot, by itself, imply m(M*M)<=2m(M), much less a uniform quadratic saving. Input information can tend to zero. No numerical search is involved.

An explicit rational example is u=1/4, t=11/256. It has

    m=27/256, h=3/256,
    h-m^2=39/65536>0,
    m(M*M)=13863/65536,
    2m-m(M*M)=-39/65536<0.

The exclusion branch uses a negative observation channel. These mixtures have not been realized by exclusively positive broadcast trees, so this is a counterexample only to the proposed moment-only sufficient condition.

## 2. The constraint h>=k4 is not closed under positive products

A single positive symmetric channel of parameter lambda has posterior amplitudes lambda times the three roots of unity, hence h=lambda^3>=lambda^4=k4 for 0<=lambda<=1. Nevertheless its two-copy conditional product can leave this class.

Take lambda=4/5. The two reported labels agree with actual joint probability 19/25. Conditional on that event, the posterior is a rotated single-channel posterior of amplitude s=56/57. The labels differ with probability 6/25; the posterior is a rotated exclusion-direction posterior of amplitude w=-4/9. These follow directly from the Bayes denominators 1+2lambda^2 and 1-lambda^2; the amplitudes are (2lambda+lambda^2)/(1+2lambda^2) and -lambda/(1+lambda).

Consequently

    h_product=(19/25)(56/57)^3+(6/25)(-4/9)^3,
    k4_product=(19/25)(56/57)^4+(6/25)(4/9)^4,
    h_product-k4_product=-6671744/375015825<0.

The incoming law has h-k4=64/625>0. Both branches are genuine positive channels, so this directly refutes product closure of the candidate class h>=k4. It does not refute a weaker or more elaborate preserved constraint, nor the capacity target.

## Validation and use

The mixture identity and asymptotic sign in (1) are proved algebraically above. Python's exact rational arithmetic checked only the two displayed, analytically selected examples; there was no parameter scan. No theorem depends on floating-point output. The next three-state attempt must use more than a finite quadratic lower bound on the third moment, and cannot assume h>=k4 is preserved. No independent proof or contribution review has been run on this note; it is supporting research only.
