# Exact layer payoff and the remaining two-law budget

PREFREEZE / no nominee. One investigated family, Source111. These calculations do not freeze or replace R113, assign an independent grade, or modify any old scope. Original prose is offered under CC BY 4.0; original code under MIT. Protected source/primary/history material remains private under original rights.

## Full question and strongest credited baseline

Retain the actual I113/I119 R113 quantifiers: every known finite labeled matroid M, every known K>=1, arbitrary independent finite nonnegative S_e~Q_e and V_e~D_e with D_e/K<=Q_e<=K D_e as Borel measures and finite E OPT_M(V). The rule gets exactly S before arrivals and its independent seed, but no laws, likelihoods, extra training samples or concealed random bits. Every measurable ordering adversary may use all S,V, the laws and the complete seed. The desired absolute c>0 is uniform in n, rank, K and all laws, with reward >=(c/K)E OPT_M(V); rational observations require polynomial cost on every execution in n, observation bits and log K. Arbitrary real observations have the measurable-rule interpretation. There is no bounded-spread, fixed-rank or restricted-support replacement.

Pinned Source111's full seven mathematical sections are read and stipulated true, including reverse-query certificate operations, both residual encodings and the final whole-path rank telescope. Its exact-law guarantee is paid. I22 §3 already implements its largest density maximizer by a cardinality-perturbed integer submodular minimization, without enumerating flats. I113's full robust construction pays 2^-295 K^-27, and its likelihood-aware rejection calibration pays 2^-293/K when the additional oracle is allowed. I116 and I119 preserve those old results and their dispositions. This round does not regrade them.

I119 already integrates the strongest useful partials: an offline 1/(K+1) local-filter optimum, weighted residual-family entropy, and a joint safe-mass Bayes calculation with only one leading K. Its subsequent rank conversion, baseline/residual/path costs and test-rate comparison remain unpaid at linear loss. Bounded-spread greedy, an unconditional sample-greedy rank-polytope bound, or a separately correct fixed-prefix exchange algorithm does not supply that missing operation. In particular the existing failed sample-basis flag and double-thinning examples are credited, not repeated as new evidence.

The new calculation below replaces an intermediate safe-label count by the EXACT worst-order payoff of the executable layered rule. It is a standard matroid-greedy/multilinear reduction. It leaves a statistical budget unpaid, not a new full theorem.

## 1. Exact worst-order payoff after preprocessing

Use Source111's main architecture, or I113's same architecture with its stated parameters. For analysis fix

 Theta=(M,W,H,Dmask,C,parity),

where W is the glued vector (sample on the sacrificed mask H union Dmask union C, online value elsewhere). Fixing W is an analysis step; it is not information supplied to the algorithm. The nominal and final paths, listed groups, and each label's candidate/birth/parity tests are now fixed. Crucially none uses the eligibility mask T.

Let L_b be precisely the set passing all executable tests for final layer (b-2,b] EXCEPT membership in T. This excludes sacrificed labels, unlisted groups, baseline births and labels already in the preceding final flat. Put P_b=Fhat(b-2). Then L_b is contained in Fhat(b). It is a restriction of the contracted matroid M/P_b. Every label belongs to at most one L_b. Let r_b(A)=r(P_b union A)-r(P_b).

For a nonnegative finite weight vector v on L_b, define

 g_b(A)=min {sum_(e in I) v_e : I subset A, |I|=r_b(A), r_b(I)=|I|}.

An empty or rank-zero set has value zero. On each T realization the actual greedy algorithm returns a basis of L_b intersect T in this minor: after all eligible arrivals, any rejected element is still spanned by the selected set, since the base and accepted span only grow. Source feasibility already proves the union over b independent, at every prefix and for every interleaving.

Therefore every arrival order has reward at least sum_b g_b(L_b intersect T). Equality is achieved by ordering all eligible labels in increasing v, with deterministic ties, and placing all other labels anywhere. Within each layer this is the classical minimum-basis greedy scan. Augmentation proves that each weight-prefix has the largest possible independent cardinality, so its final basis has minimum weight. A single global increasing-v order achieves all layer minima simultaneously. Thus

 min_pi reward_main(Theta,T,pi) = sum_b g_b(L_b intersect T).       (1)

This is an equality with the minimum INSIDE all expectations, so there is no fixed-order/almighty-order substitution. It remains true when the adversary knows unused observations. For compatibility with the source take v=u, its rounded weights. For v=W on unsacrificed labels it is also an exact identity for actual reward. The latter identity alone does not remove a rounding loss in a subsequent source benchmark comparison.

The equality can be evaluated from a fully realized state by sorting and rank queries. Computing it for analysis is not an online algorithm that learns future weights.

## 2. Rank tails and an exact insertion cost

For any fixed minor with rank r_P and fixed nonnegative weights, let A_<x={e in A:v_e<x}. Every basis of A contains at least r_P(A)-r_P(A_<x) elements of weight at least x. Increasing-weight greedy attains this lower bound simultaneously for all thresholds except irrelevant endpoints. Integrating gives

 g(A)=integral_(0,infinity) [r_P(A)-r_P(A_<x)] dx.                 (2)

The integral is finite for finite A with finite weights. This is a rank-tail identity for MINIMUM bases, not the familiar maximum-independent-set rank integral used in I119's local-filter deficit.

For j not in A define tau_j(A) as the least x>=0 for which j belongs to cl(P union {e in A:v_e<=x}); set tau=+infinity if j is not spanned by P union A. In the loop case j in cl(P), tau=0. If j raises total rank, every basis of A+j must contain j and its other elements form a basis of A, so the value increases by v_j. Otherwise total rank stays fixed. In (2), adjoining j only increases the low-weight rank for thresholds v_j<x<=tau. Thus exactly

 g(A+j)-g(A) = v_j                         if tau=+infinity,
              -(tau-v_j)_+                 if tau<+infinity.    (3)

Ties change no integral. This also proves the formula without appealing to an unexamined exchange selection. A cheap element can decrease the minimum-basis payoff by replacing a more valuable basis element; a test mask is not a monotone reward input.

For example, in rank one A={a} with v_a=H and v_j=1<H, insertion loses H-1, although it changes no total rank. The reverse example A empty gains v_j. A proof retaining only rank-increase terms would discard a real negative contribution.

## 3. Exact rate interpolation at payoff level

Conditional on Theta let T(p) have independent coordinates with probabilities p_e. Define

 Phi_Theta(p)=E_T sum_b g_b(L_b intersect T(p)).

This is a finite multilinear polynomial. Coordinates outside all L_b do nothing. For an eligible j, in its unique layer let A_j be all other active eligible labels and let tau_j=tau_j(A_j). Differentiating the polynomial, using (3), yields

 partial_j Phi(p)
 = v_j P_(p,-j)(tau_j=infinity)
   - E_(p,-j)[(tau_j-v_j)_+ 1_(tau_j<infinity)].                 (4)

This computes the derivative with j absent from A_j. It makes no claim of independence between tau_j and all preprocessing; that preprocessing is fixed.

For arbitrary reference rates c and implementable rates t, put p(z)=c+z(t-c), 0<=z<=1. The exact integral of (4) is

 Phi(t)-Phi(c) = integral_0^1 sum_j (t_j-c_j)
   {v_j P_(p(z),-j)(tau_j=infinity)
    - E_(p(z),-j)[(tau_j-v_j)_+ 1_(tau_j<infinity)]} dz.         (5)

In particular Phi(t)>=Phi(c)-L_up-L_down, where

 L_up = integral_0^1 sum_j (t_j-c_j)_+
            E[(tau_j-v_j)_+ 1_(tau_j<infinity)] dz,
 L_down = integral_0^1 sum_j (c_j-t_j)_+ v_j P(tau_j=infinity) dz. (6)

No union bound over sampled safe labels is used here. There is one insertion cost per eligibility coordinate in its actual layer. The costs already include all higher-weight competitors through the bottleneck tau_j. The replacement term need not be controlled by the inserted label's own weight: H-1 versus1 in the rank-one example is unbounded.

## 4. Composing with the strongest heterogeneous source operation

Write r_e=dQ_e/dD_e. Under the SAME I113 common-sacrifice gluing law, condition on W,H,Dmask, before exposing C. The guard rates are

 c_e=t                                       if H_e=1 or Dmask_e=1,
 c_e=t r_e(W_e)/(1-t+t r_e(W_e))               otherwise.       (7)

They are independent across labels. As an ANALYSIS reference, choose T^c independently of C given W,H,Dmask with these same coordinate rates. Then the source hybrid has exactly the ordinary transition law: departing coordinates receive independent test bits at their own c_e, surviving unqueried C bits keep the same c_e, and the full transcript exposes only queried bits. The source heterogeneous disjoint-certificate lemma and deterministic containment therefore pay the squared-hazard safety comparison with no min-rate substitution. This is a compatible operation, not dismissed because rates differ across labels.

T^c is not executable without the unknown r_e(W_e). Its purpose is to identify what must be compared to the real independent rate-t tests. Conditional on Theta it still has product rates c, so (5) applies. In particular, for eligible labels,

 t-c_e = t(1-t)(1-r_e)/(1-t+t r_e).                            (8)

Only r_e<1 can contribute to L_up, and only r_e>1 can contribute to L_down. These are the two signs of the actual measure mismatch, not simultaneous replacement of all rates by c_min and c_max.

There is an additional exact measure identity, useful but insufficient. On an unsacrificed coordinate H_e=Dmask_e=C_e=0, the joint law of its glued weight and this triple is

 (3/8)(1-t) D_e(dw).

Hence integrating an eligible-coordinate term with (8) replaces its coefficient by

 (3/8)t(1-t)^2 (D_e-Q_e)_+(dw)/(1-t+t r_e(w))

for L_up, and the same expression with (Q_e-D_e)_+ for L_down. The remaining function of w and other data is unchanged, including eligibility, layer assignment and the bottleneck. This is a density identity, not independence of that function from w. For arbitrary Borel laws the positive variations mean (1-r)_+D and (r-1)_+D, respectively.

One cannot silently fix the layer while integrating w: changing w may change its listed weight group, its nominal birth and its layer. For an unsacrificed label its own value did not build the paths, but it DOES determine which fixed path/group is queried at arrival. The piecewise dependence must stay in the integral.

Even the matched-rate reference needs additional accounting. Independent heterogeneous test thinning gives, for any fixed rank witness I,

 E r(T^c intersect S | P) >= sum_(e in I) c_e,

and one may maximize that sum over independent I in S over P. This standard weighted matroid-greedy comparison is paid. It does not turn the old unweighted safe count into a matched-rate welfare theorem for free. The source residual family, I119's weighted residual budget and combined safe mass still must be connected to these weighted witnesses, and all baseline, small-group, maximum-branch and later-path costs still must be paid. None is hidden in Phi(c).

## 5. A loss that occurs in the actual layer architecture

The negative term is not an artifact of ignoring preprocessing. Consider rank one on four parallel nonloops, with rounded weights (1,1,H,H), H a power of the source rounding base. Let Hmask be empty, Dmask={first low,first high}, C empty, parity even, and kappa>1. Each listed group has exactly one density datum. Its density map fixes the loop flat, all nominal births are0, and the preceding final flat at-2 is the loop flat. The two unsacrificed labels, one low and one high, are both eligible in layer0.

Take the low unsacrificed label's likelihood at weight1 to be1/K and the high label's likelihood to be1. Such a low law is realized by D(1)=K/(K+1), Q(1)=1/(K+1), with the complementary atom at0; both measure bounds hold. The other three labels can have their displayed weights deterministically with Q=D. All stated masks and this weight realization have positive probability. Thus (7) gives c_low=t/[K(1-t)+t], c_high=t.

Here the exact conditional mean is Phi(q_low,t)=q_low+Ht(1-q_low). Consequently

 Phi(t,t)-Phi(c_low,t)=(t-c_low)(1-Ht).                         (9)

It is negative whenever H>1/t. This includes the SOURCE constants kappa=2^100, t=2^-140, B=2^32, H=B^5. The finite diagnostic also uses a readable t=1/8,K=8,H=64 example. This shows the loss term must be retained even for a genuine positive-probability source preprocessing state. It is NOT a lower bound against R113, an unconditional failure of the source rule, or a proof that a rank-budget method cannot work. Other states, the maximum branch and positive interpolation terms may pay the loss.

### Why a uniform conditional comparison cannot finish this route

The same source-compatible construction extends to m unsacrificed low labels, one sacrificed low label, one sacrificed high label and one unsacrificed high label, all parallel. There are still exactly TWO listed groups with one density datum each; kappa>1 keeps both density maps trivial below time0 regardless of m. Let every unsacrificed low have the normalized two-point laws above, independently. On the positive-probability event that their glued weights all equal1, Hmask is empty, Dmask is the specified pair and C is empty, every unsacrificed label lies in the same layer0. This is an actual conditional state, not an arbitrary layer invented outside the source architecture.

For a common low test rate q and high rate t, the exact payoff expectation is

 Phi_m(q,t)=1-(1-q)^m+Ht(1-q)^m
           =1+(Ht-1)(1-q)^m.                                  (10)

Indeed any tested low forces minimum-basis weight1; if none is tested, the high contributes H precisely when its test is positive. Put c=t/[K(1-t)+t]. For any fixed K>1 and 0<t<1, c<t. Letting H tend to infinity through powers of the source base gives

 Phi_m(t,t)/Phi_m(c,t) -> [(1-t)/(1-c)]^m.                      (11)

The right side tends to zero as m grows. Thus no positive factor depending only on K and t can compare Phi(t) to Phi(c) on EVERY source preprocessing state. In particular a uniform conditional c0/K comparison of this specific matched-reference/actual-test pair is false, even for fixed K=2 and the source's actual constants. All m,H used in any counterexample are finite, and the associated distributions have finite expected optimum.

This does NOT refute an unconditional comparison: the conditioning event's probability can be exponentially small, other states contribute, the maximum branch remains present, and an algorithm may change its preprocessing/selection. Nor does it contradict the exact-law source theorem, which integrates preprocessing and has r=1. It identifies precisely why replacing the missing global budget with a pointwise-in-Theta inequality would be an invalid closure. The signed mixed-measure integral in(5), or a genuinely different law-free algorithm, must do additional work.

A second attempted closure charges every low insertion to a displaced high basis label using classical exchange. Along a fixed insertion sequence those charges telescope along replacement chains, but the total can consume the whole original high-basis value, as(10) shows. Dropping positive rank-creation terms in(5) and asserting that exchange alone consumes only a fixed fraction is therefore unjustified. Known-law balanced thresholds pay that fraction by distributional prices; the fresh primary proof explicitly uses those prices and independence of the next value. Neither input is supplied here merely by writing a bottleneck threshold.

## 6. What remains unpaid

The most direct sufficient continuation of this approach is an UNCONDITIONAL comparison of the executable branch mixture to E OPT_D, using (5) or its lower bound (6), with all matched-reference, residual, path, rounding and maximum-branch terms included, at a single absolute c/K. Neither Phi(c) nor E(L_up+L_down) has the required full-scope bound here. Known likelihoods would implement the separate paid rejection-calibration route, but are absent from R113.

The old I119 Boolean-pivotal overload is therefore not asserted solved. Equations(1)–(8) give an alternative, exact payoff-level formulation and retain negative replacement costs that a naive rank argument loses. Classical greedy sensitivity and product differentiation completely explain these identities; their proof length, sharper description and finite checks are not evidence of substantial contribution. No universal law-free scale allocation, one-K budget, full author proof, frozen theorem or restricted nominee emerged.

Primary comparison: ABHM2609.19118v1 §5 supplies exact exchange sensitivity and a fair-orientation/fixed-prefix invariant; it is not an invariant for biased unknown orientations or a prefix selected from the full seed/data. FSZ2507.09507v1 §2 supplies a correct product-activation, rank-polytope, balanced-spanning-chain interface and Theorem2.5 proof; sample-greedy activations still do not satisfy its product and conditional-rank hypotheses simultaneously. KW1201.4764v1 §§2–3 supplies balanced thresholds and a full exchange/rank-price proof, with known laws and online weight-adaptive ordering that does not see unseen values. Its surplus identity uses independence from the arriving value, which is not available for a full-data-selected prefix. These are precise contract differences, not claims that every modification of these methods fails.

The calculation is durable research evidence only. All old full targets and dispositions remain unchanged, and no current-open, priority, exhaustive-search, all-method impossibility, correctness/contribution grade or acceptance/count claim is made.
