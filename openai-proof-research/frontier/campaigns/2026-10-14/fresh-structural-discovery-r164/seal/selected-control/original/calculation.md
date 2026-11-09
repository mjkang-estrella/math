# Prefreeze calculation: variance-sensitive eligible thinning

This is a sustained feasibility calculation inside the fully read Source157 linear-list proof, not a frozen nominee or an independently graded theorem. No old target is changed. Primary Liu–Luo v2 was fully read before this calculation; Gu–Xu v1 §§1–2 and the pertinent routing material and Girão–Narayanan's complete paper were read as well. The classical variance-sensitive martingale proof of Freedman was read during development, before writing this note; that read is late relative to the initial idea, not an antecedent invented after the fact. Its original publisher URL returned HTML, and an identified mirror of the original 1975 article was used. OCR equations were checked against rendered original pages101,106–108.

## 1. Fix exactly the source experiment

Let P be finite, f(P)<=r, with |V(P)|<=n, r>=1. The source bounded sampling lemma gives independent stable sets I_j, each of size<=M=ceil(n/r), with every vertex marginal1/(2r). Fix eligibility sets E_j BEFORE sampling. Define W=V(P)\union_j(I_j intersect E_j). Distinct repetitions W_i use wholly independent trials; within one trial, vertex indicators need not be independent. All arguments below preserve this distinction.

The naive source concentration envelope is a change of at most2M vertices when one trial is replaced. Using that envelope for every observable produces variance scale q N M². There are two stronger compatible calculations.

## 2. Fractional chromatic observables have unit sensitivity

For any fixed A subset V(P), put F=f(P[A intersect W]). If trial I_j is replaced by another stable set I'_j, each one-sided difference of the two remainders is a subset of one stable set. Fractional coloring is monotone and subadditive over a partition of the vertices. Hence each direction of the difference in F is at most1: |F-F'|<=1, regardless of M or n. This already permits the source bounded-difference lemma with b=1.

There is also a conditional-variance proof that will clarify the count calculation. Fix every trial except j, and form W^- by omitting the deletion at j. Choose an optimal fractional dual w on P[A intersect W^-]. Extend w by zero to all vertices of P. This extension is feasible for the full graph: the intersection of any stable set of P with its support is a stable set of the induced graph. Therefore sum_v w(v)<=f(P)<=r. For every possible I_j,

    0 <= F^- - F(I_j) <= sum_(v in I_j intersect E_j) w(v) <= 1.    (1)

The first upper bound follows by restricting the same feasible dual to the smaller remainder; the last follows because I_j is stable. The weights depend on the other trials but NOT on I_j. Equal marginals imply

    E_(I_j) (F^- - F(I_j))²
      <= E_(I_j) sum_(v in I_j intersect E_j) w(v) <= 1/2.         (2)

Now reveal trials in order. With past fixed, average over future trials. Write g(x)=E_future F(past,x,future), and c=E_future F^-(past,future). The future is independent of x. Jensen and the fact that variance minimizes squared distance to a constant give

    Var_x g(x) <= E_x(g(x)-c)²
                <= E_future E_x(F(x)-F^-)² <=1/2.                (3)

Also the range of g is at most1, so each Doob difference has absolute value<=1. Thus deterministic predictable-variance bound N/2 holds. The same reasoning works for f(P[A intersect W_i]) in any one copy. There is no exchange of an adaptive optimizer with an unconditional expectation: w is selected with trial j omitted and held fixed while averaging that trial.

## 3. Fixed-set counts: a variance bound linear in M

Take any fixed A, a=|A|, and either Z=|A intersect W_i| or Z=|A intersect union_i W_i| for at most q independent copies. There are s<=qN independent trials. Again omit one trial, obtaining Z^-. Omitting it can only enlarge W_i and hence the union. Pointwise,

    0 <= Z^- - Z(I_j) <= |A intersect I_j| <= M,
    E_(I_j)(Z^- - Z(I_j))² <= M a/(2r).                          (4)

For a single-copy count one can take s=N. For a union count, the other copies merely determine which newly exposed vertices actually change the union; the upper bound by |A intersect I_j| remains valid. No independent-vertex assumption is made. For two trial values, both counts lie in [Z^--M,Z^-], so their difference is at most M, not2M. The Jensen argument in (3) gives the deterministic bounds

    |Doob difference|<=M,
    sum of predictable conditional variances <=V=s M a/(2r).    (5)

These estimates retain the exact dependence on a. They do NOT assert an a-independent replacement of the source's all-subset concentration statement.

## 4. Classical martingale step, fully compatible

Freedman1975, §§3–4, especially (3.2)–(3.5) and (4.1), supplies the exponential-supermartingale operation. For a finite centered Doob martingale with increments bounded in absolute value by b and deterministic predictable-variance bound V, its published bound after scaling, applied to each sign, gives

    P(|Z-E Z|>=u) <=2 exp[-u²/(2(V+b u))].                       (6)

If V=0 the martingale is constant. One may obtain the familiar slightly stronger denominator2(V+bu/3) directly: for 0<=lambda<3/b, the exponential series and j!>=2*3^(j-2) for j>=2 give

    E(exp(lambda D)|past)
       <= exp(lambda² E(D²|past)/(2(1-lambda b/3))).

Iteration and lambda=u/(V+bu/3) prove that form, with the negative tail treated identically. Nothing in the calculation needs this stronger constant; use the actually read published form (6) throughout.

Substituting (3) or (5), respectively, yields

    P(|F-E F|>=u) <=2 exp[-u²/(N+2u)],
    P(|Z-E Z|>=u) <=2 exp[-u²/(s M a/r+2M u)].                  (7)

The sampling distribution and eligibility sets remain exactly those of the source. This is a classical conditional-variance composition, not a new concentration theorem.

## 5. Integrate EVERY place where the source uses concentration

Use the source constants unchanged: D0=10^6 gamma, Q0=401², B satisfying its explicit lower bounds, y=max(1,t/r), x=floor(r/200), q=ceil(t/x)², k=ceil(D0 t y), N=ceil(B r log(2y)). The range is still

    t/log t <=r<=4t,   1<=y<=log t,
    t/y<=r<=4t/y,  q<=Q0 y²,  k<=(D0+1)t y.                    (8)

For this feasibility calculation allow the larger order envelope

    n <= t^(3/2)/(log t)^5,                                    (9)

only for sufficiently large t. This is a calculated envelope for the SAME intermediate thinning operation, not a proposed new substantial theorem. Put nbar=max(n,t); for sufficiently large t it too obeys (9). Then

    M<=2 nbar y/t,   N<=(B+1)r log(2y).

Every count set actually used in the source has a<=2k:
- separator or small-leaf vertices in the fixed deterministic decomposition;
- the k preselected neighbors of one vertex in H;
- the at most k/4 endpoints of one fixed cut-test matching.
No count on an arbitrary unbounded A is silently included.

Consequently s<=qN and (5) give

    V <= 2 Q0(B+1)(D0+1) nbar y^4 log(2y).

For u=delta r with any of the finitely many positive fixed deviations used by the source, M u<=8 delta nbar. Equations(6)–(8) therefore give a tail at most

    2 exp[-c_delta t²/(nbar y^6 log(2y))].                     (10)

Here c_delta>0 depends only on delta and the already fixed source constants. Fractional-chromatic observables instead have a tail at most

    2 exp[-c'_delta t/(y log(2y))].                            (11)

The decomposition is chosen before samples, has O(n²+1) nodes by the source potential argument, and every separator/small leaf has at most2k vertices. Both (10) and (11) dominate a union bound over those polynomially many nodes. Therefore the source fixed-region argument, including its auxiliary clique blow-up and ordinary connectivity extraction, is unchanged. No minor exclusion is asserted for that auxiliary blow-up.

The source private-model argument is also unchanged. Select dual weights after one entire W_i alone, never after all success events. Independence of other copies gives expected lost weight at most(q-1)p of its weight; Markov and union bounds give4q(q-1)p+o(1). The fixed B gives q²p<=10^-4, where p<= (2y)^(-B/4). These estimates have no n term.

For complement connectivity, the cut-test matching family is fixed BEFORE the q copies. Its logarithmic size is

    O((1+n/k) log²(2n)) <= C(log²t + nbar/t * log²t).

Under (9), this is O(log²t + sqrt(t)/(log t)^3). The negative exponent in (10), even at worst y=log t, is at least

    c sqrt(t)/(log t * log(2 log t)).                          (12)

The ratio of (12) to sqrt(t)/(log t)^3 tends to infinity, as does its ratio to log²t. Thus the full cut-test union bound tends to zero. The fixed-neighbor tests also pass. The source grouping theorem can now join the same retained private-model bags: unchanged 2xq<k/64 and floor(k/32)>=gamma(2xq) pay all ports. This produces the same forbidden K_t model under the hypothesis that every remainder has f>r/2. The tested intermediate thinning conclusion therefore closes throughout (9), with the same stable-set size cap M and the same r/eligibility quantifiers.

Finally, applying the source global palette-bin construction at this order has no new obstacle: its occupancy failure is at most(J+2)n exp(-c t/log t), still o(1); the cleanup miss bound is n t^-8, also o(1). The bin count stays O(t) and color identity remains global. All intermediate remainders inherit the eligibility condition. This recovers a linear small-graph list bound in the larger calculated range, but the source FINAL theorem already proves a linear list bound for EVERY order. No stronger final coloring theorem has been obtained.

## 6. Why this is not a nominee, and the actual limits

The paid calculation is: source bounded stable-set sampling + a stable-set/LP marginal sensitivity bound + the classical Freedman conditional-variance inequality + the source's unchanged finite cut tests, private models, grouping and palette assignment. An apparent need for a new concentration theorem disappears after this strongest compatible reduction. Neither the larger exponent in (9) nor the length of this derivation by itself identifies a substantial operation beyond existing machinery. No contribution or correctness grade is assigned here.

The test-family comparison retains a real limitation. In this argument the negative exponent is of scale t²/(n polylog t), while the logarithm of the matching-test family is of scale(n/t)polylog t. Taking n as large as t² does not make this union estimate close. This is a limitation of THESE estimates, not an impossibility result, an all-order-thinning conjecture nominated as a finding, or a claim that no compatible classical refinement exists. A truly new unrestricted-order thinning or an additional coloring/model conclusion would need a paid replacement for that comparison or a different structural mechanism; neither has been supplied.

No DP/online/multifold extension is inferred. The eligible sets are fixed in advance; they are not an adversary's online choices. Global colors have genuine identity, unlike arbitrary correspondence covers. No claim is made for prescribed weighted demand functions. The sampled-set bound and all root/linkage/footprint conditions remain those explicitly analyzed. I22's full all-cover target and every other frozen old scope remain untouched.
