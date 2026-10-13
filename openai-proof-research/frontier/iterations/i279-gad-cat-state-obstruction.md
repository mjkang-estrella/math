# I279: cat states obstruct summed marginal coercivity

Parent analytic diagnostic, 2026-10-12. **Technical route obstruction, not an accepted finding.** This refutes the sufficient condition (LP) proposed in I273, for every fixed interior GAD parameter pair. It does not refute I273's actual uniform pure-state stability target (U).

## Exact construction

Use I273's channel A=A_(gamma,nu), with 0<gamma,nu<1, t=1-gamma, h=nu(1-nu), and minimum output entropy s0. Let

    a=sqrt(1-nu)|0>+sqrt(nu)|1>,
    b=sqrt(1-nu)|0>-sqrt(nu)|1>,
    z=<a,b>=1-2nu,
    psi_n=(a^tensor n+b^tensor n)/sqrt(2(1+z^n)).

Since |z|<1 this is well-defined. Both a and b are minimum-output vectors by the actual pinned family-276 minimum-output formula; the retained I273 paper's channel definition and minimum-output statement are the dependencies. No upstream truth is audited.

For every site j the marginal of psi_n is diagonal, with entries

    (1-nu)(1+z^(n-1))/(1+z^n),
    nu(1-z^(n-1))/(1+z^n).

Indeed, the two diagonal product terms contribute P_a+P_b, and the two cross terms contribute z^(n-1)(|a><b|+|b><a|); both sums are diagonal. Thus

    det rho_j = h(1-z^(2n-2))/(1+z^n)^2 -> h>0,
    sum_j det rho_j ~ n h.                                  (1)

## The entropy excess stays bounded

Put sigma_a=A(P_a), sigma_b=A(P_b), and X=A(|a><b|). In the computational basis,

    X = [[(1-nu)(1-2gamma nu), -sqrt(t h)],
         [sqrt(t h), nu(2gamma(1-nu)-1)]].

Its trace is z and its determinant is gamma h(1-4gamma h)>0. For a two-by-two matrix, ||X||_1^2=Tr(X*X)+2|det X|. Substitution gives

    ||X||_1=kappa=sqrt(1-4gamma h)<1,
    kappa>|z|.

Define tau_n=(sigma_a^tensor n+sigma_b^tensor n)/2 and omega_n=A^tensor n(P_(psi_n)). By multiplicativity of trace norm on tensor products,

    ||omega_n-tau_n||_1
       <= (|z|^n+kappa^n)/(1-|z|^n).                      (2)

To justify entropy continuity with all dimension factors explicit, let delta=||rho-tau||_1/2 and write rho-tau=delta(R-S) for states R,S from the positive and negative parts. The state (rho+delta S)/(1+delta) equals (tau+delta R)/(1+delta). Entropy concavity and the binary-mixture upper bound, applied to these two representations, give

    |S(rho)-S(tau)|
       <= delta log d+(1+delta) h_2(delta/(1+delta)),        (3)

where h_2 uses natural logarithms. The estimate is sufficient here and no sharp continuity constant is needed. With d=2^n and (2), its right side tends to zero.

Both component product outputs in tau_n have entropy n s0, so the binary-mixture upper bound gives S(tau_n)<=n s0+log 2. Hence

    0<=D_n(psi_n)<=log 2+o(1).                             (4)

Equations (1) and (4) already disprove the existence of any finite C(gamma,nu) in I273's proposed bound sum_j det rho_j<=C D_n for all pure inputs.

In fact D_n(psi_n)->log 2. Measure Pauli X on each factor of tau_n. Under its binary component label the outcomes have opposite means +/-m, m=2sqrt(t h)>0. The sign of their sample average has error at most 1/(n m^2), by Chebyshev. Its mutual information with the equally likely label tends to log 2, by the binary error-entropy bound. The standard Holevo bound then implies S(tau_n)-n s0>=log 2-o(1). Combine with the mixture upper bound and (3).

## What this does and does not settle

The actual target (U) asks for d_n(P_psi)^2<=K D_n(psi), where d_n is trace distance to a product of minimum-output latitude states. The present family has D_n->log 2, not zero, and d_n^2<=4, so it is not a counterexample to (U). Its one-site marginals tend to diag(1-nu,nu); trace-distance contraction under partial trace gives liminf d_n>=2sqrt(h)>0, consistent with a nonzero bounded defect.

The product-projector union bound in I273 cannot be made uniform by summing marginal determinants: a single collective cat variable correlates all sites while costing only one bit of output mixing entropy. A viable proof of (U) must avoid paying that same collective defect once per site. The alternative relative-entropy route, or a direct global overlap estimate, remains open in this record.

This is a parent analytic calculation, not an independent acceptance gate or a novelty claim. No numerical scan was used. The preserved source records and I273 explain the entropy conventions and channel parameters. Follow-up should test (U) itself, not spend further effort proving the false condition (LP).
