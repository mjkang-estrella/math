# r55 — no eligible substantive discovery; credit 0

Research performed solo on 2026-10-29, approximately 15:32–15:40 UTC. Root owns all acceptance and counts. Observed campaign counts are 6 additional / 36 total. No nomination, Lean work, paper or PROOF.md.

## Exclusion reconciliation and three literal primary questions

Read the ancestor and batch AGENTS.md, complete ledger/prior-context JSON and NEXT.md; hashes and accepted/excluded inventory are in context-screen.json. Respect all user exclusions, particularly accepted six families, active polyomino and r54 structural/spectral lane, beta-median r53, real Mathieu, and the listed exhausted special-function/combinatorial families. No Nuttall target appeared in the shared context or lane SUMMARY title search. This is a fresh lane, not an assertion of worldwide novelty.

The three screened questions all come from the literal body of John Nuttall, *Determinantal approach to a proof of the Riemann hypothesis*, arXiv:1111.1128v1, submitted 2011-11-04 13:48:09 UTC. Current abstract/history still lists only v1. Downloaded PDF and extracted body are saved with SHA256 in provenance.json.

1. Conjecture 1, §4.3 p11: for every integer order r>1 there is a finite integer m(r) such that the kernel K(u,v;m(r)) built from the m(r)-fold tail integral of the actual Riemann Phi is reverse-rule sign-regular RR_r. The actual published continuation, *Wronskians, Cumulants, and the Riemann Hypothesis*, Constructive Approximation 38 (2013),193–212, DOI10.1007/s00365-013-9200-8, online 2013-06-27, retains it in §4.5 p209. Read actual published statement, RR3 Theorems2.2/3.5 and final discussion. The author's later *Cumulants, the Riemann Hypothesis, and Similar Problems*, Theorem5.6, proves the analogue for the different Conrey–Ghosh Theta1 function. Read its literal Theta1 definition and theorem/proof opening: this is NOT a proof for the Riemann Phi. The full original all-order uniform cumulant result remains unresolved here; no bounded small-order computation could settle it. Not selected over the explicit algebraic mechanism below.
2. Conjecture 2, §6.1 pp15–16: for every integer r>1, with mu(r)=r(r−1)/2 and epsilon_r=(-1)^mu(r), the polynomial epsilon_r W_r(y) has degree mu(r+1) and positive leading coefficient. W_r=det[p_(i+j−1)(y)]_(i,j=1..r), p1=2y−3. Rejected as public/routine. The author's *Basic Wronskians in the Riemann Hypothesis*, dated October2012, §1.3 explicitly supplies the classical bilinear Wronskian identity (Karlin p60 Eq4.2), and §3 Theorem3.1 claims an explicit all-order polynomial form for the beta(y)=2y−3 case. Its differential generator y*d/dy−y and the source generator 4y*d/dy+5−4y differ only by derivative rescaling and exponential conjugation, so their order-r determinants differ by the positive factor 4^(r(r−1)). Independently, the classical identity immediately proves the degree/sign claim as described below. No attempt to claim correction of any printed explicit coefficient formula.
3. **Selected for serious attempt:** Conjecture 3, §7.2 pp24–25, Eqs7.15–7.24: for every integer r>2, every i=0,...,r(r−1)/2−1, every m=0,...,r(r−1)−2i−2, and every normalized symmetric monomial index j=1,...,np(m), the literal expansion coefficients C(i;m,j) vanish. This is independent of Phi or its moments (source Remark7.1). Selected because formal Gamma-ratio coefficients are finite-order differential operators. The reduction below covers the full literal quantifiers, but is a classical helper/corollary mechanism, not an eligible substantive discovery under the user's rules. Stop investment; credit0.

## Exact normalization bridge for selected Conjecture3

Work in Q[t1,...,tr][[y]], let M=r(r−1), and let S denote average over all permutations of the t variables. Put d_a=q(a)−a for a permutation q of {1,...,r}. Source Eq7.17 is

    R_q(t) = S product_a t_a^(2(d_a+r−1)).

All exponents are nonnegative. Its normalization corresponds to the common polynomial

    Q_r(y)=product_(a=1..r−1) [(1+2ay)(1+(2a−1)y)]^(r−a).

For an integer d define formal rational series

    H_d(y)=product_(k=1..2d)(1+ky)^(-1)                  (d>=0),
    H_d(y)=product_(k=0..−2d−1)(1−ky)                    (d<0).

This is exactly N^(2d)*Gamma(N+1)/Gamma(N+2d+1), y=1/N. Source Eq7.15 and cancellation of sum d_a=0 yield the polynomial kernel whose monomial expansion defines C:

    F_r(y,t) = Q_r(y) sum_q sign(q) product_a H_(d_a)(y) R_q(t).

No asymptotic approximation or Gamma analytic continuation is used. To check directly, each signed permutation component z_q=Q_r product H_d is the literal finite polynomial

    z_q(y)=product_(a=1..r) product_(k=2(q(a)−a)+1..2(r−a)) (1+ky).

This formula follows by clearing row denominators Gamma(N+2(r−a)+1); those row factors multiply to Q_r. Empty products are1, and factors with k=0 are harmless. check.py uses this finite product directly, independent of the formal operator argument.

At y=0, alternation twice gives the exact identity

    F_r(0,t)= S[product_a t_a^(2(r−a)) det(t_a^(2(b−1)))_(a,b)]
            = (-1)^(M/2)/r! * product_(a<b)(t_b²−t_a²)².

For example r2 gives minus one half of (t2²−t1²)², fixing the normalization and sign.

For every l>=0, h_l(d)=[y^l]H_d(y) is a polynomial in d of degree <=2l. A direct proof covers positive and negative integer d uniformly: set S_j(n) to the polynomial sum 1^j+...+n^j, uniquely extended by S_j(0)=0 and S_j(n)−S_j(n−1)=n^j. Finite differences (or the falling-factorial basis) show deg S_j=j+1. The two finite products above both have

    log H_d(y)=sum_(j>=1) (-1)^j S_j(2d)*y^j/j.

For negative n, S_j(n)=−sum_(k=n+1..0) k^j, which verifies the same identity directly. Expanding the formal exponential, a contribution to h_l indexed by a partition of l has degree at most sum(j+1)<=2l. h0=1; h1(d)=−d(2d+1). These statements concern rational polynomials and formal series only.

Let E_a=t_a*d/dt_a. Since E_a acts on each monomial in R_q before averaging with eigenvalue 2(d_a+r−1), the coefficient-i operator

    [y^i] product_a H_((E_a/2)−r+1)(y)

is a polynomial differential operator of total order <=2i. The whole product is invariant under permuting variables, so it commutes with S. Consequently F_r is Q_r times this formal operator applied to F_r(0,t). Every coefficient at y^i is a polynomial differential operator of order <=2i applied to the displayed Vandermonde square (and lower-order such terms from Q_r).

Set t_a=1+x_a. Each difference t_b²−t_a²=(x_b−x_a)(2+x_a+x_b) vanishes to total x-order1, so the square product lies in the M-th power of the maximal ideal (x1,...,xr). Polynomial differential operators of order k map that ideal power into its (M−k)-th power: each partial derivative lowers total order by at most1, while multiplication by polynomial coefficients cannot lower it. Thus

    [y^i x^alpha] F_r(y,1+x) = 0 whenever |alpha|+2i<M.

This is slightly stronger than the requested |alpha|<=M−2i−2. Source symmetric monomials mu(m,j) form a basis degree by degree; their normalization changes coefficients only by nonzero rational orbit factors. Therefore literal C(i;m,j)=0 throughout the full source range. Choice of tau in t_a=tau(1+x_a) contributes only the common homogeneous factor tau^(2M), already removed in Eq7.19, and has no bearing on zero coefficients.

## Why this is not nominated

The source itself identifies C3 as an algebraic auxiliary cancellation relation, independent of its analytic Phi problem. The argument is the standard symmetrized alternant/Vandermonde square plus the elementary fact that a differential operator of order k lowers diagonal vanishing by at most k. It does not prove the needed analytic asymptotics, positivity of D(n,r), or cumulant sign-regularity. The strongest substantive objection is precisely that this is a routine classical helper; the user's explicit exclusion applies even if no exact prior statement has been located. No novelty PASS or acceptance recommendation.

The Wronskian calculation has an equally direct classical exclusion. Write D=4y*d/dy and W0=1,W1=2y−3. Bilinear condensation gives

    W_(r+1) W_(r−1)=W_r D²W_r−(DW_r)²−16r y W_r².

If W_r has degree r(r+1)/2 with leading coefficient c_r, the last term uniquely controls the top degree; c_(r+1)c_(r−1)=−16r c_r². Induction from c0=1,c1=2 proves the source degree and epsilon sign, using exactly the identity already printed in the October2012 follow-up. This is uncredited independent rediscovery, not a second outcome.

## Falsification and limits

Run `sh run.sh`. Hard caps AS512MiB, per-process and sampled group CPU210s, wall230s, BLAS threads1, sampled process-group RSS512MiB,40ms sampling. 515 exact integer cancellation checks passed: all monomial orbits in the stronger forbidden region for r2,3,4, and all m<=6 forbidden orbits for r5. Explicit finite z-products are checked, not numeric Gamma evaluations. Source CV recurrence versus literal Hankel determinant was independently compared through r4, and the bilinear recurrence degree/sign checked through r7. Finite tests are diagnostics only. The boundary cannot be strengthened to <=M: at r2,i0 the x1² coefficient is −2. This exact boundary witness is the strongest falsifier of overextending the cancellation argument; it is not a source counterexample.

Actual scientific gap: full Riemann-Phi cumulant sign regularity requires an all-r finite m(r) with uniform u>=0 positivity of every order p<=r; this lane supplies neither that uniform estimate nor a counterexample. The Theta1 theorem cannot be transferred by naming analogy. No formal obligations proposed, since nothing survives the substantive gate. A formalization of the cancellation bridge would only certify a rejected routine helper.

## Current sources, chronology and registry limits

Primary body2011, October2012 basic-Wronskian companion, 2013 published body and author companion corpus were obtained. Published PDF is actual Springer bytes, not inferred from an abstract. Author's March2013 progress report retains the cumulant program; later cumanal_a proves Theta1 analogue only. No exact date for cumanal_a was reliably established; do not infer chronology from web crawl dates. Frame report body is separate and assumes the cumulant conjecture. Other author reports beyond the saved six companions were not exhaustively body-read.

At 15:33:14UTC five current repository heads were fetched. Omega dev advanced from user r53 baseline fae48cc... to 3b4135a35caa0ae817cf5eca51d605b098027fd2 (commit15:32:31UTC). Other four heads unchanged. Complete named cached Omega D5/Problems and other repository scopes were hash-verified and lexically screened; they are not the complete dev tree. The21-commit comparison returned all21 commits but hit GitHub's300-file cap. Missing delta files were NOT cleared. Registry-screen.json explicitly records this gap. The new CriticalThetaTailPeak body concerns an actual signed theta-tail Laplace critical peak; the cached PoschlTellerCoefficientVanishing is a different Bernoulli/logarithmic spectral coefficient question; the arithmetic Wronskian module is polynomial Hasse-Wronskian independence. Their definitions/theorem signatures were inspected; they do not supply the source C3 formula. Other lexical hits were not exhaustively body-read. No complete current-registry absence or universal priority claim.

Current MathDB322494/322495 pages saved at15:36UTC; empty solution indicators are not novelty evidence. Bounded title/author searches and their source URLs were used only as leads; all relied-on mathematics is in saved primary bodies. No access403/429/challenge was encountered or retried. The successful Springer responses have cookie-error query parameters in their final URLs, but valid PDF bytes/body were returned; no bypass used.
