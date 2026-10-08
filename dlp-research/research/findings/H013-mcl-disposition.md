# H013 MCL: conditional correlation reduction, no predictor yet

2026-10-08. Factory Opus5.5 proposer; independent native Sol identity/sampling
review, native Astra backend/cost review, Claude Opus5.5 character-bound review.
All completed, read-only. Raw Factory and bound reports retained separately.
Root checked identities and primary bilinear-bound statement. Paper mathematics,
not new Lean claims. Verified improvement NONE; no experiment or training run.

## What survives

Let E have prime-order subgroup <G> of size q, Q=kG!=O, H=F_q^*, and fixed
public f:E->C with |f|<=1. Let chi:H->complex mu_m have exact order m.
Define F(n)=f(nG), c_chi=E_H F(n)*conj(chi(n)). Substitution proves

    E_c f(cQ)*conj(chi(c)) = chi(k)*c_chi.
    c_chi(f,uG) = chi(u)*c_chi(f,G).

The second identity uses the SAME fixed f, not a retrained generator-dependent
feature. Magnitude is a property of curve, encoding, feature AND character.
If f(-P)=f(P) and chi(-1)=-1, then c_chi=0 exactly. The latter is equivalent
to (q-1)/m odd. This null is a cheap falsifier for those particular features.

A nonzero correlation can identify a multiplicative coset if estimated finely
enough. It is not itself an algorithm producing such a feature. No named cheap
f with an adequate correlation guarantee has been supplied in the original card.

## Sampling, calibration and validation repairs

Set X(0)=0, X(c)=f(cQ)*conj(chi(c)) for c!=0. Draw r uniform in F_q and s
uniform in F_q^*. For L<=q, c_i=r+i*s are pairwise uniform-distinct, not iid.
With alpha=q/(q-1), Z=alpha/L * sum_i X(c_i) is unbiased and

    E|Z-chi(k)c_chi|^2
      = alpha^2*(q-L)/(L*(q-1))*Var_Fq(X) <= alpha^2/L.

Do not discard zeros silently. Independent progression blocks and coordinate-
wise medians yield O(epsilon^-2 log(1/delta)) observations with justified
confidence; a full q-point nonzero-stride block is exact. Pay two scalar starts
per block, additions, feature evaluation, character conversion and precision.
Pairwise independence alone does not give the raw exponential tail.

Nearest-phase decoding compares the target estimate to zeta_j*estimated_c_chi.
A sufficient condition is epsilon_G+epsilon_Q < |c_chi|*sin(pi/m), where both
calibration and target errors include numerical error. Calibration must resolve
the same fine phase separation; estimating magnitude alone is insufficient.

For a multiplier multiset S, let D_S=E_(u in S,n in H)|F(un)-chi(u)F(n)|^2.
Fourier orthogonality gives

    D_S=2 sum_eta (1-Re E_S (eta*conj chi)(u))*|c_eta|^2.

For lambda_S=max_(rho!=1) Re E_S rho(u)<1, this implies
|c_chi|^2 >= ||F||_2^2-D_S/(2*(1-lambda_S)). IID uniform S of size K satisfies
Pr(lambda_S>1/2)<=(q-2)*exp(-K/8) by Hoeffding/union bound. This gap event holds
for every feature simultaneously; S may then be used for training. Empirical
defect/norm estimates still need fresh validation after feature selection, or
explicit adaptive confidence accounting. With one-sided errors t_N,t_D, a valid
lower bound is max(0,Nhat-t_N-(Dhat+t_D)/(2*(1-lambda_bar))). Validation observations
are bounded by1 and4 respectively. Charge point generation/dilation/precision.
Selecting among multiplier sets or holdouts is not free confidence amplification.

## Character evaluation and remaining search are paid

Choose and certify primitive g in F_q^*, h=(q-1)/m, zeta=g^h and lambda=g^m.
To turn c^h=zeta^j into chi(c)=exp(2*pi*i*j/m) requires extracting j: an order-m
discrete log or a paid m-entry roots/index table. Exponentiation alone does not
produce a complex phase. Charge factorization/order certification, g search,
table construction/storage, exponentiation, lookups and complex precision.
Known training scalars provide computable labels, not cost-free labels.

After identifying j, set k0=g^j. A concrete coset BSGS stores [lambda^a]G for
0<=a<B and queries [lambda^(-bB)*k0^-1]Q for 0<=b<ceil(h/B). Equality gives
k=k0*lambda^(a+bB); verify. If h even, an explicitly signed x-only construction
can reduce the enumerated coset exponent range to H=h/2; otherwise H=h.
With actual fixed-base costs v_G,v_Q, search is

    B*v_G + ceil(H/B)*v_Q + lookups + scalar bookkeeping.

Ignoring ancillary costs, its minimum is about2*sqrt(H*v_G*v_Q). Both fixed-base
tables, B collision keys/indices and character advice occupy memory. A claimed
comb cost omitting doublings is not automatic: positional tables trade paid
space/setup for additions. No constant-step coset-rho walk was specified.
Raw 20--30 addition-equivalent costs and 14x illustrations are hypothetical.

Let C_pre be all work of one attempt including training/calibration, setup,
failed phases, search and verification. For a fixed instance, with success
probability s and an independent fresh baseline of expected work W0 on failure,
E[total]=C_pre+(1-s)*W0. A gain requires C_pre<s*W0; 10% requires
C_pre<=(s-0.1)*W0. For random targets with varying s_d,W0(d), use
E[C_pre(d)+(1-s_d)*W0(d)], NOT a product of average failure and average cost.
Uniform bounds are another valid option. No predictor currently passes this gate.

## Bound/prior-art review: retain scope, not unsupported exclusions

Root read [Ahmadi--Shparlinski Lemma2](https://arxiv.org/pdf/1302.4210), which
restates their earlier bilinear bound for ordinary curves. With both index sets
F_q^*, weights chi and subgroup order q, U=(q-1)S by multiplicativity. At nu=1,
|S| << q^(5/6)*p^(1/12)*(log p)^(1/3). Thus when q~p, normalized correlation
for an additive phase of x is O(q^(-1/12)*(log q)^(1/3)). This exponent is prior
art, not a new result. The original2010 paper was not independently read here.

The raw reviewer also rederived a log-free small-multiplier bound. Restrict its
elementary full-curve character-sum argument to #E(F_p)=q (not an arbitrary
subgroup without an additional subgroup-sum theorem). For 1<=v<v'<=V and
2V<p, h=x o[v]-x o[v'] has double poles; coefficients at common poles differ
because v!=+/-v' modp. It is nonconstant and not Artin--Schreier. A character-sum
bound then leads to |S|^2<=q^2/V+8q V^2 sqrt(p). The balancing choice
V~(q/(8sqrt p))^(1/3) suffices for O(q^(-1/12)) when q~p; it is NOT the exact
calculus optimum (the raw review calls it that). Constants and integer rounding
are not used for any performance conclusion. General subgroup extension of
this elementary proof was not established by the review.

For Phi(x), the bound scales with the nonconstant additive Fourier l1 norm.
That norm may grow enough to make it vacuous; arbitrary learned features are
not bounded this way. Rational-degree/multiview extensions need their own pole
and exception checks. The bound does not exclude the card's hoped-for signal.
Prime FULL order q>=5 excludes trace0 supersingularity over p>=5; a mere prime
subgroup does not, correcting the raw review's overly broad ordinarity wording.

Neither exact Aff(F_q) subgroup classification nor published Legendre-oracle
attack upper bounds prove all methods have three forms or order-two oracles
are useless. Both exclusions remain unsupported. A planted Re(chi) control has
coefficient1/2 only when chi^2!=1; for order two it has coefficient1.

## Decision and next falsifier

Preserve as a conditional reduction, not a discovered attack or rejected class.
Native coordinate/arithmetic and group-action/learning followups independently
seek actual cheap f and a full-cost gate. No broad training/FFT engine authorized.
The proposed twelve-curve sweep at orders near2^12,2^14,2^16,2^18 already exceeds
the total1M-event cap on nominal point enumeration alone, before feature/FFT/
field/setup work. It is not a bounded falsifier as proposed. Finite fitted decay
cannot establish an asymptotic rejection. Next meaningful test requires a named
feature, predicted useful correlation regime, frozen validation and a paid cap.
