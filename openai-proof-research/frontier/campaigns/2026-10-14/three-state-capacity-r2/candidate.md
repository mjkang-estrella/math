# Three-state capacity, second attempt: unresolved

Date: 2026-10-14. Status: **the original arbitrary-tree capacity criterion remains unresolved; no new substantial frontier result proposed.** The argument below is a technical obstruction to a natural changed-potential family. It does not refute the capacity criterion or the possibility of a smaller universal positive quadratic-saving coefficient. No acceptance count is changed.

## Target and exact remaining estimate

The target is the uniform-root symmetric three-state broadcast on an arbitrary deterministic bounded-degree rooted tree, with independent known edge parameters `0 < lambda_e <= 1`, all level-n spins observed, and `R_v = product_[root,v] lambda_e^2`. The proposed capacity is

    C2 = sup { flow mass : nonnegative conserved flow theta to infinity,
          sup_ray sum_(e=(v,w)) (1-lambda_e^2) theta(e)/R_w <= 1 }.

I319 already proves, in the larger locally finite scope,

    m_infinity >= C2/(1+C2),

where `m = E |p0 + omega p1 + omega^2 p2|^2` is half the posterior chi-squared information. This is the standard electrical linear-estimator direction and is not claimed again. Perfect edges have zero resistance; a perfect root ray gives infinite capacity and information one. A perfect tail behind a noisy prefix need not give infinite capacity. On a locally finite tree, infinite capacity is equivalent to a wholly perfect root ray. The zero-capacity finite-tree convention is as in I319.

Let G be the class generated from revealing and uninformative posterior experiments by positive channels and finite conditional products. For independent marginal complex posterior means u,v put

    a=E|u|^2, b=E|v|^2, h_mu=E Re(u^3), h_nu=E Re(v^3),
    s=u conjugate(v)+conjugate(u) v, N=u+v+conjugate(u)conjugate(v).

The precise unpaid estimate remains, for some absolute c>0 and every mixed pair in G,

    E [ |N|^2 s^2/(1+s) ] <= (1-c)ab + 2(h_mu b + a h_nu).  (U)

Use the continuous zero-normalizer convention from I319. I319 proves that U would imply necessity by a quadratic change of variable and a conserved-flow extraction; it does not prove U. The positive-generated-parent three-leaf example with edge parameters `(1/4,4/5,4/5)` refutes c=1, with excess `119807/175001400`. Its weak-channel limit bounds any possible universal c above by `8735449/9152433`. Those are existing supporting obstructions, not this round's contribution. Neither that example nor this round refutes some c>0.

## Technical proposition: the centered-log quadratic correction cannot supply a global potential

For a strictly positive likelihood vector l=3p with coordinate average one write

    I(l) = average(l log l),
    J(l) = (1/2) average((l-1) log l),
    u_i(l) = log l_i - average(log l),
    B(l) = (1/2) average(l u^2).

For a law mu put i_mu=E I, j_mu=E J, b_mu=E B. Consider the four-parameter family

    Phi(mu) = alpha i_mu + beta j_mu + gamma b_mu + delta j_mu^2,  (1)

where all four coefficients are fixed real numbers.

**Proposition.** There are no such coefficients and k>0 for which all three properties hold on every strictly positive finite positive-tree-generated experiment:

1. `Phi(mu) >= k m(mu)`;
2. `Phi(mu star nu) <= Phi(mu)+Phi(nu)` for every pair, including distinct laws;
3. `Phi(E_lambda mu) <= lambda^2 Phi(mu)` for every `0<lambda<1`, where E_lambda is the positive edge operation.

The countertests use only one-leaf and two-leaf positive-channel trees. This excludes a finite-dimensional approach to the target, not other potentials, channel-dependent coefficients, bounded-support restricted classes, multistep inequalities, or a positive-generated polynomial cone. It is not a capacity counterexample.

**Proof.** The exact mixed identities, derived next without an identical-law recursion, are

    j_(mu star nu) = j_mu+j_nu,
    b_(mu star nu) = b_mu+b_nu+4 j_mu j_nu,
    i_(mu star nu) = i_mu+i_nu-H(mu,nu),                    (2)

where H is the mutual information between the two observations under their actual joint marginal. Conditional independence given the uniform spin gives `0 <= H <= log 3` by data processing. For two nontrivial single positive channels H>0: their joint marginal density relative to independent uniform labels equals `1+2t^2` on agreement and `1-t^2` on disagreement, so is nonconstant.

To derive (2), centered logs add under the normalized product. Under input i, Bayes tilting and label symmetry give `E[u_i|S=i]=2j` and `E[u_i^2|S=i]=2b`. Conditional independence then gives the first two formulas, including the factor four. Expanding the log of the product-normalized likelihood gives the third; H is the normalizer's expected log under the joint law. Every experiment used below is finite with strictly positive coordinates, so no integrability or limit exchange is needed to establish (2).

Consequently

    Phi(mu star nu)-Phi(mu)-Phi(nu)
      = -alpha H(mu,nu) + (4gamma+2delta) j_mu j_nu.        (3)

Let C_t denote a single observed channel of parameter `0<t<1`, and put

    L(t)=log((1+2t)/(1-t)).

Its likelihood orbit is `(1+2t,1-t,1-t)`, whence direct calculation gives

    m(C_t)=t^2,
    i(t)=[(1+2t)log(1+2t)+2(1-t)log(1-t)]/3,
    j(t)=t L(t)/3,
    b(t)=(1+t)L(t)^2/9,
    V(t):=b(t)-2j(t)^2=(1-t)(1+2t)L(t)^2/9.              (4)

As t approaches one, `j(t)` diverges, `i(t)` tends to `log 3`, and `V(t)` tends to zero. Applying product subadditivity to `C_t star C_t` in (3), the boundedness of H forces `2gamma+delta <= 0`. In contrast, if `2gamma+delta < 0`, (4) makes `Phi(C_t)` tend to negative infinity quadratically in L(t), contradicting property 1. Therefore

    delta=-2gamma.

Now (3) is just `-alpha H`. Since H is strictly positive for any `C_t star C_t`, property 2 forces `alpha>=0`. Formula (4) rewrites `Phi(C_t)=alpha i(t)+beta j(t)+gamma V(t)`. Its nonnegativity as t approaches one forces `beta>=0`.

At zero, the convergent Taylor expansions of the elementary logarithms give

    i(t)=t^2-t^3/3+O(t^4),
    j(t)=t^2-t^3/2+O(t^4),
    V(t)=t^2+O(t^4).                                   (5)

Fix any `0<lambda<1`. Since `E_lambda C_t=C_(lambda t)`, property 3 implies

    Phi(C_t)-lambda^(-2)Phi(C_(lambda t)) >= 0.

Divide by t^3 and let t decrease to zero. The quadratic terms cancel, yielding

    (1-lambda)(-alpha/3-beta/2) >= 0.

Together with `alpha,beta>=0`, this forces `alpha=beta=0`. Hence `Phi=gamma(b-2j^2)`. By property 1 and `V(t)/t^2 -> 1`, we have `gamma>=k>0`. Apply property 3 once more with fixed lambda and let t approach one. Its left side `gamma V(lambda t)` tends to the strictly positive `gamma V(lambda)`, while its right side `lambda^2 gamma V(t)` tends to zero. This contradiction proves the proposition. Every physical parameter in this proof stays strictly between zero and one; perfect channels are used only as limits. QED.

For the source's `F=3I-2J+(4/5)B`, the failure is already visible directly: (3), with delta=0, tends to positive infinity for two near-perfect single channels. Subtracting `(8/5)j^2` cancels its mixed log term exactly, but creates `3i-2j+(4/5)(b-2j^2)`, which tends to negative infinity on C_t as t approaches one. Thus this particular cancellation cannot be turned into a nonnegative capacity potential.

## Research disposition

The positive-generated moment cone remains unidentified. I326 already rules out a finite lower bound on the third moment alone and product closure of `h>=k4`. A multistep argument would need a proved inequality relating the separate child laws or an error that telescopes through the actual inhomogeneous tree; no such inequality was obtained. No actual tree with reconstruction and zero C2 was constructed. The source's common-law moment identity cannot be substituted for this missing work. The four-state companion's cubic preserved-cone theorem concerns a different number of states and exponent and supplies no missing three-state input.

The technical proposition is proved independently above, with exact symbolic checks retained alongside it. It is supporting failure evidence only. The strongest unconditional capacity conclusion remains I319's already-paid sufficiency. Correctness of the displayed no-go does not establish substantive contribution or worldwide priority. The next useful attempt must leave family (1), prove a genuine positive-generated mixed saving such as U, or construct a reconstruction/capacity counterexample.
