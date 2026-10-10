# I113 — Online optimization discovery: misspecified one-sample selection

Date: 2026-10-10. Premise: accept all theorems **and lower proof operations** in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream truth audit, contradiction synthesis, child agent, shared edit, staging, commit or publication.

**Disposition: no substantial finding nominated.** The main paid result P113 is an implementable, distribution-independent prophet rule for independent but misspecified samples, with reward fraction `2^-295 K^-27` under two-sided likelihood-ratio bound K. Its proof conditions the actual seed law, uses a dominated hybrid transition, and pays all residual and path costs without an exponential-in-n change of measure. A second route proves fraction `2^-293/K` if likelihood ratios are supplied; that extra information is unavailable in the chosen target. Explicit rank-one families defeat either one-sided domination assumption alone, even in a fixed order. G113 recovers exact stochastic mean-payoff values and Blackwell-optimal policies in deterministic quasipolynomial time, but has a full-scope reduction to the accepted source comparison operations. These are **author proofs**, not independently audited theorems. Their concrete lower-operation reductions warrant a technical disposition here. The stronger unknown-law target R113, fraction c/K, remains **unproved and unrefuted**. No optimality of that dependence is asserted. The accepted count remains eight.

## 1. Scope, exclusions, sources and evidence

I read AGENTS.md, upstream.json, the current four ledgers and their relevant overlap records. The four ledgers are frozen at the start of this round; their historical stale summaries do not override the current eight-count. I111's original-proof pass and technical disposition are taken from the assignment, without binding an active working file. I110/I112 outputs are not dependencies. I109 is parked and was not resumed.

The previous prophet implementation is I22 §3: exact largest-density flats via cardinality-perturbed submodular minimization, with polynomial independence queries for rational observations. I do not rename it a new finding. R011 concerns a rooted separator allowance for perfect-matching entropy; I29 concerns tight-chain normal rank and covariance trace for common-base entropy; I77 concerns weighted graph-switch mixing, conditional slices and global congestion. None is a selection guarantee for misspecified samples. P113 does not assert a matching/common-base sampler, prescribed-marginal entropy algorithm, or weighted graph-chain gap. In particular it does not split any of those findings.

The evidence uses the complete `sources/preprints-tree.json`: 13,223 entries, 749 manuscript directories and 10,373 original blob positions. The 9,340 ignored I14 originals, I79 outside originals and I88 augmented mapping are reused by immutable path/hash reference, without recursive copying or corpus downloading. The two full-domain **lexical**, not semantic, searches retain exact Python regular expressions and ordered matching-line multisets: 399 scope lines and 199 robustness lines. Their domain includes all 10,373 representations, including 776 inherited PDF extractions. Search misses are not proof of absence. The selected inventory has 94 representations from seven named families; selection is not a claim that every selected file was read. `read-manifest.json` identifies the actual readings and conventions.

The following source abbreviations refer to these exact pinned directories. Every file's raw URL, Git blob hash and SHA-256 are in `selected-inventory.json`.

- **P:** `One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026`. All seven substantive sections were read, including the endings of the reverse-exposure, marked-pivot, final-accounting and secretary proofs. Main theorem `thm:main` assumes mutually independent S_e,V_e with identical law within each pair. `prop:hidden` is a fixed-weight expected-minimum-over-orders guarantee. `lem:simulation` uses exact equality of the two coordinate laws. Lower operations used below are `lem:density`, `lem:paths`, `lem:generators`, `lem:transactions`, the reverse-map and hybrid-containment constructions, `lem:pivot-patterns`, the two-sequence residual encoding, and the order-uniform/telescoping rank comparisons. Their mechanisms, not just the headline constant, are accepted inputs.
- **S:** `Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026`. All four substantive sections read through completion. `thm:main` outputs nonnegative **expected pathwise liminf** value sets. `thm:discount` already supplies a common positional pair at all discounts `0<u<=1/(2H)`, rational gains, coefficient bounds and guarantees against arbitrary behavioral opponents. `thm:labeling` is for every monotone discounted-translation map, not only the final game's chosen precision.
- **D:** `Deterministic-quasipolynomial-time-mean-payoff-games-September-25-2026`, especially the complete §7 `cor:full-solution` and separate-player self-reductions. Its randomized companion was screened as weaker; no randomization improvement is claimed.
- **K / U:** `Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026` and `Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026`. U's full finite-table, capped-filter, shadow/fallback and scheduling proofs were read. Its `thm:main` **already** has polynomial preprocessing and per-request bit cost polynomial in `L+log(t+1)`. Its explicit activation is `2^T_P-1`, and its additive movement includes `(2^T_P-2) diam(X)`. No useful bound on this term is supplied. U's `thm:existence` records the exact imported K interface: one policy for every finite oblivious request word, zero additive loss from distinct starts. I use that stipulated interface, without claiming a complete reading of K's much larger geometric proof.
- **MP:** `Mean-payoff-parity-games-in-quasipolynomial-time-October-5-2026`. All five substantive sections read. `thm:main` concerns deterministic arenas; its lower strategy construction supplies uniform **pathwise** prefix bounds, and its small-dominion algorithm exploits deterministic attractors. It is not an almost-sure stochastic conjunction theorem.

Current primary checks were performed before fixing the final target and again against the proposed bridge. The preserved version pages display 2609.19118v1, 2507.09507v1, 2406.12799v1 and 2605.01497v1. The last also has a published ICALP 2026 version, which was fetched. Previously captured exact primary PDFs/texts are referenced, not downloaded again.

Primary comparisons:

1. Abdi–Banihashem–Hajiaghayi–Mittal, [2609.19118v1](https://arxiv.org/abs/2609.19118v1), Theorem 1.3 and complete §5 proof: one-sample 1/2 and O(n²) oracle queries for an order independent of samples/values/coins. Its conditional fair-thinning invariant fixes the arrival prefix before exposing orientations. It does not imply an expected minimum over seed-aware orders, nor a biased-orientation invariant.
2. Feldman–Svensson–Zenklusen, [2507.09507v1](https://arxiv.org/abs/2507.09507v1), Theorem 1.1 and §2 spanning-chain interface: almighty sample-based OCRS with rank-dependent sample count; the prophet conversion requires additional samples. Fu et al., [2406.12799v1](https://arxiv.org/abs/2406.12799v1), Appendix C through its ending, bounds balanced **CRS** with unknown activation vector: `c <= 1/M + M^((s+1)M)/N`. This does not prohibit a one-sample welfare guarantee. P113 does not construct a constant-selectable one-sample OCRS. No oracle lower bound is evaded by assuming an exponential feasibility rule: the actual algorithm is implemented by I22's explicit SFM operation.
3. Dütting–Kesselheim, [EC 2019, pp.111–129](https://paulduetting.com/pubs/inaccurate-priors_EC19.pdf), especially the full proofs of Theorems 5.1 and 6.1 and their ending examples. These compare policies under approximate **known** priors, with bounded values and additive errors growing with n. They do not state the unknown-law, one-sample, dimension-independent multiplicative comparison below. No numerical ranking of this problem is inferred.
4. Coester–Cosson, [ICALP 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.65), Theorem 1 and Propositions 4–7: polynomial implementation and bounded support on HSTs, plus an extra log n for arbitrary metrics. The tree support/rounding interface is not a general-metric implementation of K at its n-independent ratio.
5. Chatterjee–Doyen–Gimbert–Oualhadj, [Perfect-information stochastic mean-payoff parity games](https://lsv.ens-paris-saclay.fr/~doyen/papers/Perfect-Information_Stochastic_Mean-Payoff_Parity_Games.pdf), **limsup-average**, largest-recurring-priority almost-sure objective, positive-attractor and increasing-phase interfaces: its algorithm has the factor `d n^(2d) MeanGame`, not a quasipolynomial bound when d is unrestricted. The source S expectation theorem and MP pathwise theorem cannot simply be identified with this objective.

A real named connection is the **single-sample matroid prophet problem / matroid secretary conjecture**. P's introduction and the primary FSZ introduction explicitly discuss that connection. The [ORdős problem page](https://ordos-problems.github.io/problems/single-sample-matroid-prophet.html) also records it, but its older status is not treated as a current novelty certificate or as MathDB. No verified matching MathDB page was obtained in the bounded search. The relevance of R113 is stability of this one-sample information interface when historical and online laws differ, not a claim to solve the classical secretary conjecture anew.

## 2. Four exact screened targets

**P / chosen R113.** Does there exist an absolute c>0 and, for every known K>=1, a distribution-independent measurable rule for every finite oracle matroid, with exactly one independent sample S_e~Q_e and online V_e~D_e per label, all 2n variables independent, `K^-1 D_e <= Q_e <= K D_e` as measures and finite expected optimum, such that every measurable order depending on all data and the full seed has expected reward at least `(c/K) E OPT(V)`? On binary rational observations require polynomial oracle/bit cost in n, total observation length and log K. P113 pays a polynomial K-loss, not this linear loss. No claim that 1/K is optimal; it is the explicit benchmark attained by Route B when extra likelihood information is supplied.

**K / useful uniform service.** For every finite binary rational metric, `2<=k<n`, repeated starts permitted, seek one oblivious-adversary policy with `E cost <= C log²(k+1) OPT + p(n,k) diam(X)`, polynomial preprocessing and polynomial per-request cost in input length alone, with C absolute and p a fixed polynomial. U already rules out nominating bare computability or polynomial-in-log-time service. Its complete scheduling proof leaves exactly the useful startup bound unpaid. Coester–Cosson do not remove log n on arbitrary metrics. No new fractional transport or small-support construction was found in this screen; do not claim this target is disproved.

**G / exact Blackwell output.** For every explicit finite turn-based stochastic game in S's binary model, compute exact rational expected-liminf values and both pure positional strategies simultaneously optimal against all behavioral opponents, and optimal for every normalized discount `0<u<=1/(2H)`, in `2^O(log²(L+2))` bit operations. This is technically closed by the full source comparison mechanism; §7 below pays the precision and gives a concrete reduction. Source headings alone would misleadingly suggest an open exact-output gap.

**SP / stochastic conjunction.** For the same finite binary stochastic arena with integer priorities and rewards, decide the set of starts from which Max has one strategy enforcing `P(liminf average>=0 AND least recurring priority even)=1` against every behavioral opponent in deterministic quasipolynomial time in the full input length. Unbounded memory is allowed. This is an actual extension beyond S and MP. The observed old positive-attractor recursion has an `n^(2d)` budget for its **limsup**-average objective; it is not a theorem for the requested liminf objective. Reversing priorities by an even constant changes largest to least recurring priority, but does not change limsup to liminf. Thus both the objective bridge and the quasipolynomial recursion are unpaid here. The deterministic source's bounded-length attraction and pathwise prefix bounds are not stochastic quantitative budgets. This target remains only screened, not developed or refuted in this round. P was chosen for its concrete local comparison mechanism and independently testable quantitative partial.

## 3. Route A: a full robust product-mask construction

### 3.1 Theorem P113 and information model

Let `K=2^m`, m a nonnegative integer. For every finite labelled matroid M on n labels there is one rule depending only on M and K such that the following holds for **every** collection of Borel probability laws D_e,Q_e on finite nonnegative reals satisfying

`K^-1 D_e(A) <= Q_e(A) <= K D_e(A)` for every Borel A and every e.  (LR)

Let all S_e~Q_e and V_e~D_e be mutually independent, with `E OPT_M(V)<infinity`. The rule receives S and uses an independent seed. For every measurable permutation chosen from M, the laws, S,V and the complete seed, it irrevocably accepts an independent set A and

`E sum_(e in A) V_e >= 2^-295 K^-27 E OPT_M(V)`.  (P113)

For rational observations it uses polynomially many independence queries and polynomial bit operations in n, the total length of the observed rationals and m, on every execution. It does not receive densities, distribution descriptions, support bounds, extra samples or secret coins. General real observations have only the finite measurable-rule claim, not a finite-precision Turing claim. Empty matroids, loops, rank zero, ties and zero weights are included.

The theorem concerns independence, not correlated observations. The guarantee is a ratio of expected welfare, not a high-probability realized-optimum ratio. A general real K can be replaced by the least power of two at least K; this changes the displayed bound by at most `2^27`.

### 3.2 Actual rule, including the common sacrificed mask

Set

`B=2^32 K^4`, `kappa=2^100 K^8`, `t=2^-140 K^-12`,

`s=t/K=2^-140 K^-13`, `eta=2^-12`, `gamma=eta/(16K)=2^-16/K`.

Draw independent masks H,D,C,T with rates `1/2,1/4,t,s`, independently across labels; draw a fair branch and fair parity. **In both branches sacrifice B0=H union D union C.** Only S on B0 is used; all online values on B0 and all other samples are ignored.

In the maximum branch, use the highest-priority positive nonloop among the revealed B0 weights as threshold; accept the first unobserved positive nonloop of strictly higher rounded-weight/label priority, and accept no more. If the threshold set is empty, every positive nonloop exceeds it.

In the main branch use P's fixed-vector algorithm with exactly the above B,kappa, guard rate t and test rate s. For clarity, its executable instructions are these. Round a positive observed weight down to `u_e=B^floor(log_B w_e)`, with zero separate. A candidate e is a positive label outside H not spanned by H's higher-priority labels. Group candidates by rounded weight; only groups meeting D are listed, in increasing weight order `G_1,...,G_l`. The revealed data determine `D_h=D intersect G_h` and `C_h=C intersect G_h`; full groups are proof variables only.

For each flat P0 let Q_h(P0) be the largest flat containing P0 maximizing `|D_h intersect Z|-kappa r(Z)`. Put `a_h=-3h`, enable Q_h at auxiliary times k>=a_h and use the identity earlier. Starting with F_0(k)=loop flat for k<0 and E for k>=0, set

`X_h(k)=Q_(h,k)(F_(h-1)(k))`,

`F_h(k)=cl(X_h(k) union (C_h intersect X_h(k+1)))`.

For an arriving unsacrificed candidate in listed group h, find its birth `b=min{k:e in X_h(k)}`. Reject unless e is in T, `b>=a_h+2`, b has the chosen parity, and e lies outside F_l(b-2). In that layer accept exactly when it increases rank over `F_l(b-2)` and the already accepted labels of the layer. The accepted union is independent for **every** weight/seed/order realization: each layer is independent over its preceding flat, and all earlier layers lie in that flat. This is precisely P's pathwise feasibility construction, valid for the changed positive integer kappa and B>1. No probabilistic guarantee is used to obtain feasibility.

### 3.3 The exact posterior law (new deduction A113)

For analysis define `W_e=S_e` on B0 and `W_e=V_e` outside B0. The execution just specified is exactly the fixed-vector execution on W, with all accepted weights equal to the actual V_e. This is a pathwise induction on arrivals, even if the adversary sees unused observations.

By (LR) write `r_e=dQ_e/dD_e`, choosing a version in `[1/K,K]` outside a D_e-null set. Let

`p=P(e in B0)=1-(1/2)(3/4)(1-t)=5/8+3t/8`.

Thus `5/8<=p<=3/4`. The joint density of a mask triple z=(H_e,D_e,C_e) and W_e=w, relative to D_e(dw), is its original product probability times `r_e(w)` if z is nonzero and times one if z is zero. Therefore, conditional on the full W vector, mask triples are independent across labels, with kernel

`P(z | W_e=w)=P_orig(z) r_e(w)^(1_(z!=0)) / [1-p+p r_e(w)]`.  (A)

This statement follows by multiplying the coordinate densities and normalizing; it holds for atoms and arbitrary Borel laws. The branch, parity and T are still independent of W and of these triples. In particular, the two branches really are a fair mixture **after** conditioning on W. Using P's different sacrificed masks in the two branches would not justify this assertion.

For any original product distribution tilted by r on an event and 1 on its complement, the largest-to-smallest tilt is at most K. Every event of original probability q therefore has posterior probability between q/K and Kq; its complement has probability at least `(1-q)/K`. This follows by bounding the numerator by the minimum/maximum tilt and the denominator by the opposite extreme. It remains true after fixing coordinates, since the restricted original law stays product and the tilt still has the same two values.

Consequently, conditional on W:

- H bits are independent and their rates q_e satisfy `1/(2K)<=q_e<=1-1/(2K)`.
- Given H, D bits are independent and `P(D_e=1|H,W)>=1/(4K)`; the conditional C marginal is at most Kt.
- Given H,D, C bits are independent, with rates `t/K<=c_e<=Kt` (the upper bound may be capped at one). If H_e or D_e is one, c_e=t exactly.
- Given H and masks outside a fixed H-defined group, its O=D union C indicators are independent and each has probability at most `1-1/(2K)`: originally `P(O)=1/4+3t/4<=1/2`, so the complement retains at least `1/(2K)`.
- T is an independent product mask of rate s, including after these conditionings.

We never claim H,D,C are mutually independent under (A). In particular, revealing D changes the posterior guard rate on a candidate label.

### 3.4 Candidate budget under the posterior

Fix W and write u for its rounded vector, `Wopt=OPT_M(u)`. Let I* be priority greedy on all positive labels, `Y=I* minus H`, and U be the candidate set. The deterministic source fact `Y subset U` and independence of Y continue to hold.

By the H complement lower bound,

`E_H u(Y) >= Wopt/(2K)`.

For each label, condition on all higher-priority H bits. The test that these labels do not span e is now fixed and is independent of H_e. Its expected contribution when H_e=0 divided by its expected contribution when H_e=1 is `(1-q_e)/q_e<=2K`. In the latter event, e is selected by greedy on H. Summing over positive labels gives

`E_H u(U) <= 2K E_H OPT_M(u|H) <= 2K Wopt`.  (B)

This is an exact nonuniform-mask replacement of P's fair candidate identity, with no product K^n loss.

### 3.5 Dominated hybrid transitions (new deduction B113)

Fix W,H,D. All groups and density maps are now fixed (the guard-dependent paths are not). Write `K_(h,b)=union_(j<h)[T_j intersect (X_j(b) minus X_j(b-1))]`. Let sigma_h count d in D_h intersect Y with birth b satisfying `a_h+2<=b<=0`, the chosen parity, and `d notin Q_h(F_(h-1)(b-2) union K_(h,b))`. Use P's reverse computation and its predictable query transcript: at each step only departing guard coordinates are queried, no coordinate twice. Unqueried C bits retain their independent coordinate laws c_e. The ordinary transition map is increasing in the state, time and bits. Coupling fresh transitions by a product vector with these fixed rates shows that, before a given nonloop exits, its conditional exit probabilities p_b are nondecreasing in reverse time.

P's `lem:transactions` explicitly allows **independent Bernoulli variables of arbitrary rates**. Its proof charges each disjoint positive certificate to the telescoping resource `log p(V)`, and gives at most `log(1/delta)` expected certificates for an increasing event of failure probability delta. Apply its same dyadic bands `[2^(-j-1),2^-j)`, j>=12. Every survival transaction certifies the band's initial survival event using only its newly queried positives, by P's monotone reverse-map construction. Hence

`P(exit at conditional hazard < eta) <= 2^-11(14 log 2+1)<1/2`,

and summing exit masses gives

`sum_b E[1_(still present at b) p_b^2 | W,H,D] >= eta/2`.  (C)

There is no hidden uniform-rate requirement in this application: coordinatewise common coupling and the already heterogeneous certificate lemma are the only probabilistic operations used.

At one valid birth endpoint freeze the incoming state and perform the ordinary step. Conditional on its **complete** transcript, form P's hybrid: retain unqueried C bits on survivors and replace the departing coordinates by their independent T bits. The retained bits have rates c_e; replaced bits have rate s<=c_e. The conditional hybrid vector is therefore stochastically dominated by a fresh product vector with rates c_e. Since exiting an increasing flat map is a decreasing event,

`P(hybrid exit | complete ordinary transcript) >= p_b`.

The conditional probability of ordinary and hybrid exits is at least `1_(present) p_b²`, by the tower property. P's deterministic containment

`Q_h(F_(h-1)(b-2) union K_(h,b)) subset hybrid_output_h`

still holds, where K_(h,b) contains all lower-group tested labels departing at b. Its proof only uses which bits are retained/replaced and extensivity of the maps, not their laws. Thus joint exit implies the same safety exclusion as in P. The ordinary birth events are disjoint over endpoints, so no joint independence of hybrid experiments is needed.

Excluding baseline births loses at most `|D_h|/kappa`, because Y is matroid-independent and by the source generator bound `r(Q_h(loop flat))<=|D_h|/kappa`. The fair parity keeps one half. For the safe sampled statistic sigma_h exactly as in P,

`E[sigma_h | W,H,D] >= eta |D_h intersect Y|/4 - |D_h|/kappa`.

For an H-defined true group U_i of size n_i, define sigma_i=0 if unlisted. Averaging over D, including the unlisted branch, gives

`E[sigma_i | W,H] >= gamma |Y_i| - n_i/kappa`.  (D)

The original equality of hybrid and ordinary laws has been replaced by a one-sided comparison in the useful direction; pretending they remain equal would be false.

### 3.6 Quantitative residual comparison

For each listed group and valid chosen-parity endpoint define `P_(h,b)=G_h intersect (X_h(b) minus X_h(b-1))`, and set it empty at other endpoints. Write `r(A|B)=r(A union B)-r(B)`. Define `z_h=sum_b r(P_(h,b) minus O | X_h(b-2) union K_(h,b))`, exactly as in P. Choose rank witnesses Z_b and form the residual R_h of birth labels left outside their enlarged span. These are pointwise constructions. Then

`R_h subset O`, `sigma_h <= kappa z_h + |R_h|`.  (E)

The density argument proving (E) compares the largest maximizer with its extension by Z_b, so is valid for the present integer kappa. The whole-path density generators satisfy `|J_h|<=|D_h|/kappa` by the same telescoping objective difference.

Fix W,H, parity and all D,C,T bits outside U_i, without conditioning on listing. For n=n_i>=kappa put q=floor(n/kappa). In the branch z_h<=n/kappa, the density and witness unions each have at most q labels. The accepted source's two marked-sequence encoding gives a deterministic residual family with

`|Rfamily_i| <= S_q(n)^2 [4^(2q) S_(2q)(n)]²`,

where `S_d(n)=sum_(j<=d) binom(n,j)`.

Here the old sequences are fixed lower paths and lower competition sets; movable occurrences are the chosen density and witness labels. The first sequence records valid birth/parity and the second records exclusion after the witnesses; their intersection is the residual. Thus the family is fixed before **all focal** D,C,T bits, even under the tilted law. P's marked-pivot operation gives the displayed bound independently of the number of time slots. For kappa>=4, applying `S_floor(alpha n)(n)<=exp(alpha n(1-log alpha))` at alpha=1/kappa,2/kappa gives

`log |Rfamily_i| <= (1000 log kappa/kappa)n`.  (F)

The elementary binomial estimate follows from `alpha^(alpha n) S_floor(alpha n)(n) <=(1+alpha)^n<=exp(alpha n)`; hence no asymptotic floor error is hidden.

By (A), a fixed residual candidate R satisfies

`P(R subset O | W,H,outside bits,parity) <= (1-1/(2K))^|R| <= exp(-|R|/(2K))`.

Set `delta=2^-28 K^-3`. The union bound and (F) give

`P(exists R in Rfamily_i, R subset O, |R|>delta n) <= exp(-delta n/(4K)) <= delta`.  (G)

All constants hold at the smallest permitted n=kappa. To check them for every m>=0, note

`1000 log kappa/kappa <=1000(100+8m)2^-100 K^-8 <= delta/(4K)`:

use `100+8m<=108*2^m` and `108000<2^70`. Moreover `delta kappa/(4K)=2^70 K^4 >=28+3m>=log(1/delta)`, which proves the last inequality in (G).

Let e_i be residual size in the low-rank listed branch and zero otherwise. Then `E e_i<=2delta n_i`. In the high-rank branch `sigma_i<=n_i<kappa z_i`; in the unlisted branch both vanish. Thus (D)–(G) imply, for every n_i>=kappa,

`E[z_i | W,H] >= [gamma |Y_i|-(1/kappa+2delta)n_i]/kappa`.  (H)

This explicitly pays the adaptive residual; no independence of the residual selected by the masks is assumed.

### 3.7 Final-path costs, arbitrary orders and the constants

For fixed weights and all coins, in listed group h define `lambda_h=sum_b r(T_h intersect (P_(h,b) minus O) | F_l(b-2) union K_(h,b))`. For true group U_i=G_h set lambda_i=lambda_h, and set lambda_i=0 for an unlisted group. This is P's final-layer rank statistic, using focal tested unsacrificed labels and contracting all lower test competitors. Its `lem:all-orders` is deterministic and gives `N_(>=i)(pi)>=lambda_i` simultaneously for every permutation pi. Its whole-path common generator set and rank telescoping give

`sum_b r(P_(i,b) minus O | final preceding flat + competitors) >= z_i-c_i`,

where pointwise

`c_i <= |C intersect U_i| + sum_(l>i)(|C intersect U_l|+|D intersect U_l|/kappa)`.

The focal T bits remain independent of all these sets, conditional on W,H,D,C,parity and other T bits. Intersecting fixed rank witnesses with T gives

`E lambda_i >= s E(z_i-c_i)`.

Given W,H the cost is bounded by `Kt n_i+(Kt+1/kappa)sum_(l>i)n_l`. Combining with (H),

`E[lambda_i|W,H] >= (s/kappa)[gamma |Y_i|-(1/kappa+2delta+Kt kappa)n_i-(1+Kt kappa)sum_(l>i)n_l]`.  (I)

This never conditions on the adversary's order. Define analyzed groups by n_i>=kappa. Summing cumulative counts geometrically gives, for every fixed seed,

`min_pi u(A_main(pi)) >= (1/2) sum_(analyzed i) B^i lambda_i`.

Indeed each accepted B^l contributes at most `sum_(i<=l)B^i<2B^l`. The higher-group cost sums to at most `u(U)/(B-1)`. Therefore

`E[min_pi u(A_main)|W,H] >= s/(2kappa) [gamma sum_(analyzed i)B^i |Y_i|-epsilon u(U)]`,

where

`epsilon=1/kappa+2delta+Kt kappa+(1+Kt kappa)/(B-1) <=2^-25 K^-3 <=gamma/(16K²)`.

For the displayed inequality, `Kt kappa=2^-40 K^-3`, `2delta=2^-27 K^-3`, `1/kappa<=2^-100 K^-3`, and `(1+Kt kappa)/(B-1)<=2^-30 K^-4`; their sum is less than `2^-25 K^-3`.

Let m* be the highest positive nonloop rounded weight; if Wopt=0 the assertion is immediate. The discarded small groups contain total Y-weight less than `2kappa m*`. If `m*<=Wopt/(8K kappa)`, (B) yields expected analyzed Y-weight at least Wopt/(4K). Consequently

`E[min_pi u(A_main)|W] >= s gamma Wopt/(16K kappa)`.

In the complementary case use the maximum branch. Conditional on W, the B0 indicators are independent with rates in `[p/K,1-(1-p)/K]`. If there are at least two positive nonloops, the event that the top one is unsacrificed and the second is sacrificed has probability at least `p(1-p)/K²>=1/(8K²)`. On this event only the top label exceeds the revealed maximum, so it is accepted in **every** order. With one positive nonloop its unsacrificed probability is at least `(1-p)/K>=1/(4K)`, even larger. Thus its expected minimum reward is at least `m*/(8K²)>Wopt/(64K³ kappa)`.

The branch remains fair conditional on W. Its contribution in either case is at least `s gamma Wopt/(32K kappa)`: the maximum-case comparison uses `4K² s gamma<=1`. True accepted weights dominate rounded weights, and `Wopt>=OPT_M(W)/B`. We have proved

`E[min_pi actual reward | W] >= [s gamma/(32K kappa B)] OPT_M(W) =2^-293 K^-27 OPT_M(W)`.  (J)

The unconditional W law is the product of `(1-p)D_e+pQ_e`. To compare optima without multiplying likelihood ratios across labels, generate an independent V vector and, independently for each label, choose its V coordinate with probability 1-p and a Q draw otherwise. Fix an optimum I(V), with measurable finite tie-breaking. Its V-retained subset is feasible and contributes expected `(1-p)OPT(V)`. Nonnegative replacement coordinates cannot hurt this lower bound. Hence

`E OPT(W)>=(1-p)E OPT(V)>=E OPT(V)/4`.

Integrating (J) proves P113. Integrability is legitimate: each nonloop V_e has expectation at most E OPT(V); by Q_e<=K D_e its sample also has finite expectation, so the finite sum of nonloop W expectations is finite. Loop values need no moment condition. This completes the mathematical proof for every stated law and adversary.

### 3.8 Oracle and bit costs; optional unknown K

For a known flat P0 and D_h, minimize over A subset E\P0

`(n+1)[kappa r(P0 union A)-|D_h intersect(P0 union A)|]-|P0 union A|`.

It is integer submodular. A unit change in its first bracket dominates every possible cardinality change. Its minimizers are closed: adjoining a missing closure label cannot increase the primary bracket and strictly improves the final cardinality term. Primary minimizers are closed under union; their largest member is the unique cardinality maximizer. The answer is therefore exactly Q_h(P0). Rank evaluation uses at most n independence queries. Iwata–Fleischer–Fujishige's strongly polynomial SFM theorem, as used and made explicit in I22, implements this operation with polynomial bit cost because the values have O(log n+log kappa) bits. No exponential flat enumeration or representation oracle is assumed.

There are at most n listed groups and O(n) auxiliary times for each, not one step for every missing numerical weight level. All masks are dyadic, using O(n(1+m)) unbiased bits; the maximum branch uses the same already drawn sacrificed mask. Positive binary rational rounding is exact: because B is a power of two, its exponent follows from bit lengths and shifted-integer comparisons. All remaining closure, birth and conditional-rank tests are polynomial. This proves the stated worst-case implementation bound, with no polynomial claim for an unencoded real.

One rule can omit a supplied K if only expected computation is requested. Draw j>=0 with probability `2^(-j-1)`, use K=2^j, and predraw the branch/masks as above. If the actual likelihood bound is rho, let `K0=2^ceil(log2 rho)`. The j attaining K0 alone contributes fraction `2^-296 K0^-28`; other branches have nonnegative welfare and remain feasible. Every finite-j execution costs a polynomial in n, observation length and j, so geometric j gives polynomial expected cost. The draw terminates almost surely, not on every infinite random tape; this is **not** the worst-case guarantee of the supplied-K theorem. The adversary sees j too. This is a corollary of P113, not a separate finding.

## 4. Route B: exact rejection calibration and its information barrier

This route aims directly at the c/K target by discarding whole labels, instead of paying biased path costs.

**Q113 (likelihood-aware technical theorem).** Suppose, in addition to one independent sample per label, an algorithm can evaluate `h_e=dD_e/dQ_e` at that sample and knows `h_e<=K`, Q_e-almost surely. For arbitrary finite matroids and every full-seed order rule it can obtain reward fraction `2^-293/K`. Exact arithmetic/oracle evaluation is a separate computational assumption; no law-free implementation is asserted.

**Proof.** Independently accept label e into a preprocessing subset J with conditional probability `h_e(S_e)/K`. Then

`P(e in J, S_e in A)=K^-1 int_A h_e dQ_e=K^-1 D_e(A)`.

Thus J is an independent 1/K Bernoulli subset; conditional on J, its retained sample coordinates have product law D and are independent of all actual values. On the matroid restriction M|J use the accepted source P exact-law algorithm, ignoring all other labels. Its own seed is independent of data. Although the adversary sees rejection uniforms and rejected data, for each realized retained sample/value/seed its order cannot achieve less than the minimum over all retained orders; P's expected-minimum guarantee therefore applies after conditioning on J. This yields expected reward at least `2^-293 E OPT_(M|J)(V)`. Conditional on V, retain an optimal independent set's labels with probability1/K to obtain `E_J OPT_(M|J)(V)>=OPT_M(V)/K`. Integrating proves the claim. Feasibility and irrevocability are immediate. ∎

This is a genuine paid second route, but it has a precise missing input: the likelihood ratio is not available from one unknown-law sample. There is no distribution-independent scalar rejection kernel that exactly performs this calibration for all admissible pairs. Fix Q uniform on {0,1}. Both `D^+=(1/4,3/4)` and `D^-=(3/4,1/4)` meet two-sided K=2. A rule using only S, K and an independent seed has the same retained-value subprobability law on both instances; it cannot equal D^+/K and D^-/K simultaneously. This refutes that exact calibration subroutine, not all possible c/K online mechanisms. Nor does it rule out using arriving values in a different construction.

A whole-vector likelihood comparison is another inadequate implementation of this route. Relative to the hypothetical exact-sample experiment, its sample density is `prod_e r_e(S_e)`, bounded below only by K^-n. The exponential loss is real for general events: with exact law Bernoulli(1/2) and sample law Bernoulli(1/3), K=3/2 is valid and the likelihood ratio on the event that all n samples equal1 is `(2/3)^n`. Thus this particular black-box comparison cannot certify a dimension-independent ratio. It is not a lower bound on optimal prophet algorithms. Route A avoids it by reconstructing coordinate mask laws and exploiting the actual lower construction.

## 5. Falsified extensions and exact lower-bound proofs

All examples use the rank-one uniform matroid, labels arriving in the fixed order1,...,n, nonnegative bounded binary rational weights `a_j=2^(j-n)`, and an algorithm which knows n and the matroid but not the laws. They apply even with unlimited computation. Random seeds may be private, so they also apply against the stronger almighty adversary. These are information lower bounds, not matroid-oracle lower bounds.

**N113a: the upper inequality Q<=2D alone is insufficient.** For each cutoff h in {1,...,n}, let all samples be zero; for j<=h let V_j independently be a_j with probability1/2 and zero otherwise, and for j>h set V_j=0. Then `Q_j=delta_0<=2D_j` on every label. Let p_j be the probability that the algorithm selects the positive a_j on the h=n instance. Since every history through j has the same law whenever h>=j, the same p_j applies on each such instance. Since at most one positive is selected, `sum_j p_j<=1`. Its expected reward on instance h is exactly `sum_(j<=h)a_j p_j`, while `E OPT_h>=a_h/2`. If every h had competitive fraction c, then

`c/2 <= sum_(j<=h)2^(j-h)p_j` for each h.

Summing h gives `nc/2 <= sum_j p_j sum_(h=j)^n 2^(j-h) <=2`. Hence some h has ratio at most4/n. There is no positive constant uniform in n. The argument includes acceptance of zero: that can only remove future opportunities and does not invalidate the probability sum. ∎

More generally replace probability1/2 by any fixed epsilon in (0,1), keeping samples zero. Then total variation between Q_j and D_j is at most epsilon, and the same argument gives an upper bound `2/(epsilon n)`. Thus fixed small coordinate TV error does not give a dimension-independent **multiplicative** welfare ratio with unknown priors. This does not conflict with the primary additive-error results.

**N113b: the lower inequality D<=2Q alone is insufficient.** For cutoff h set V_j deterministically equal to a_j for j<=h and zero later. For **every** cutoff use the same independent sample law `Q_j=(delta_0+delta_(a_j))/2`. Then D_j<=2Q_j. The entire sample vector has the same distribution for all h. Let p_j be the selection probability at label j on the full instance h=n, averaging over samples and the seed. Again prefixes through j have identical laws for h>=j and `sum p_j<=1`. Since now OPT_h=a_h exactly, a common ratio c would imply `c<=sum_(j<=h)2^(j-h)p_j`. Summing gives `nc<=2`, so some h has ratio at most2/n. ∎

These families fail the omitted side of (LR), so they do not refute P113 or R113. In both families, supplying the actual likelihood functions reveals information about the cutoff, consistent with Route B. They also do not assert that every conceivable dependence condition is necessary; they refute exactly the two proposed one-sided classes.

No high-probability payoff claim follows from P113. Even n=1 with a value zero with probability1-epsilon and positive otherwise makes a fixed positive fraction of **expected** optimum unattainable with probability exceeding epsilon. A realized-optimum comparison is a different question and is not settled by that observation.

## 6. What is still unpaid, and why the partial is technical here

R113 asks for a constant c independent of K,n,rank and the laws with ratio c/K, with unknown Q,D and full-seed order. Route A pays only `2^-295 K^-27`; Route B pays c/K using forbidden extra distributional information. Neither the scalar-kernel obstruction nor N113a/b is a counterexample under **two-sided** bound K. In particular no numerical experiment has resolved R113.

The exact remaining task is to remove the additional K-dependent losses without querying likelihoods: either construct a law-free selection/comparison replacing calibration, or make an appropriate lower-bound family satisfying both inequalities in (LR). Merely assuming an improved safe-count inequality would restate the problem. The present proof exposes each loss: candidate retention and candidate mass, D sampling, guard-versus-test rates, residual-complexity budget, later-path costs, rounding scale and the maximum branch. Its estimates are uniform in all remaining parameters and constitute reusable paid progress.

The strongest concrete reduction defeats promotion of the polynomial-loss theorem **in this round's author assessment**. Formula (A) is Bayes conditioning of independent coordinate mixtures. The accepted certificate lemma already permits heterogeneous probabilities. The only replacement at the reverse-exposure step is the standard common-uniform coupling of a smaller product mask; deterministic hybrid containment is unchanged. P's marked-pivot family, density witnesses, telescoping rank budget and orderwise payoff conversion then apply verbatim as constructions, with the numerical inequalities (G) and (I) explicitly recomputed. I22 supplies exact SFM implementation. This is a full-scope noncircular reduction, not dismissal merely because classical tools appear or because a catalogue lacks the theorem. The source does not state P113, but its lower operations supply the mechanism once reweighted and retuned. Q113 is classical rejection sampling plus restriction; N113 is a prefix-indistinguishability stopping argument. They are technical deductions and scoped counterexamples, not several nominations.

If the parent independently judges the robustness extension to clear the substantiality gate, P113 is stated and proved in full for that assessment; this report itself neither increments the count nor claims an independent proof pass. The stronger R113 is explicitly unresolved, not nominated by renaming its polynomial partial.

## 7. G113: exact stochastic policies are already technically recoverable

Here is the concrete stronger-companion check for target G. It is included to pay the reduction instead of dismissing it by the words “rational reconstruction.”

An empty arena, if permitted, has empty output. Otherwise use S's definitions, for n>=1, integer reward bound W>=1 and product Q of all chance denominators:

`A0=n! [Q(3+W)]^n`, `H=(W+4)A0`, `N=32H²`, `lambda=1/N`.

The source already proves, for one common positional optimal pair at lambda, integer polynomials N_i(u),D(u), of degree at most n and coefficient norm at most A0, with `v_i(u)=N_i(u)/D(u)`, and its optimality for every `0<u<=1/(2H)`. It proves the resulting gains equal the expected pathwise-liminf values against arbitrary behavioral opponents. These are existence/comparison inputs, not pairs we enumerate.

At lambda, multiply D(lambda) by N^n. This is a nonzero integer d with `|d|<=A0 N^n`. Every v_i(lambda) is an integer divided by this **same** d. Each player edge expression `lambda w(e)+(1-lambda)v_j(lambda)` therefore has denominator dividing N d. Any two unequal outgoing expressions at one player vertex differ by at least

`g=1/(A0 N^(n+1))`.  (GAP)

This controls comparisons between outgoing edges, not just the gap of the mean value from zero.

Approximate the discounted vector to error at most `epsilon=g/8` in sup norm using S's exact labeling procedure. Explicitly retain Kbox=256(N+1), choose integer `Scale>=Kbox/epsilon`, set `F(t)=Scale f_lambda(t/Scale)`, `J=Scale W+N+1`, and start with a permitted box containing [-J,J]^n. The same comparison vectors `floor(Scale v)-N1` and `ceil(Scale v)+N1` have width at most2(N+1), by the discounted translation identity. The full source box-shrinking operation retains both and stops at width<=Kbox, giving error<=Kbox/Scale<=epsilon.

All these parameters have polynomial binary length in L: logA0,logH=O((L+2)²), and `(n+1)log N` is polynomial. S's mass-product recursion has O(log(n+1)) branching decreases and polynomial depth in the width exponent; its exact bound is therefore still `2^O(log²(L+2))`. Every evaluation of floor F uses only exact rational max/min/chance sums of polynomial bit length, just as in S's application proof. This is an actual precision change with the cost accounted for, not slow contraction iteration.

Choose a maximizing outgoing expression computed with the approximate vector at every Max vertex and a minimizing expression at every Min vertex. Each expression has error at most epsilon, so every selected edge is within2epsilon<g of the true extremum. By (GAP) it must attain the true extremum exactly. The selected pair's linear discounted fixed point is therefore v(lambda). S's coefficient sign-stabilization proof then makes this same pair optimal at **every** `0<u<=1/(2H)`, including exact ties: no nonzero comparison numerator can change sign in that interval. Its gain is the true mean-payoff vector in the source's expectation-of-liminf convention.

For output values, form the selected pair's polynomial matrix `Q(I-(1-u)P)` and replacing columns `Qu r`. Compute D and N_i exactly. One polynomial-time method evaluates each degree-at-most-n determinant at n+1 distinct integer points and interpolates by exact rational arithmetic; all entries, determinants and interpolation denominators have polynomial bit length by the same determinant bound with these polynomial-size evaluation points. Let l be the least nonzero degree of D. Boundedness of each quotient at zero, already proved in S, ensures u^l divides every N_i. The ratio of their coefficients at degree l, reduced as a rational, is the exact gain. This computes all values without enumerating strategies or exponentially many rational denominators.

The output pair has the source's guarantees against every behavioral opponent, simultaneously at every start. Nothing asserts almost-sure attainment of a scalar start value, a uniform finite-time convergence bound for arbitrary opponents, or a solution to a parity conjunction. This is an author-level technical theorem G113: the accepted source's determinant/sign estimates plus the accepted labeling operation already pay its full scope. No further contribution is nominated.

## 8. Verification and handoff

`frontier/experiments/i113_online_optimization_discovery/diagnostics.py` performs exact finite checks of the posterior kernels, conditional mask bounds, dominated adaptive hybrid inequality, parameter budgets, calibration identity and rank-one prefix identities. These are diagnostics, not universal proof. The mathematical arguments above handle arbitrary sizes and distributions. No independence-oracle optimizer for large instances is claimed to have been experimentally executed.

`verify.py` is an offline, read-only verifier. Run from this repository with:

`PYTHONDONTWRITEBYTECODE=1 python -B frontier/experiments/i113_online_optimization_discovery/verify.py`

It verifies the exact owned inventory (including this report and both assigned directories), immutable original and extracted-byte identities, the entire 10,373-position mapping, selected pinned references, frozen snapshots, exact search multisets, reading-passage hashes and deterministic diagnostics. Only the four explicitly listed live ledger originals may drift; their snapshots cannot. I110/I112 working outputs are not bound. It performs no download, writes, PDF extraction, bytecode generation, repair or reseal. The final seal is created only once after preseal validation; validation history is retained separately. PDF hashes certify the identity of inspected/extracted evidence, not transcription correctness or theorems.

The first preseal core replay passed: 11 frozen input snapshots, 16 immutable-reference records, all 10,373 original positions, 94 selected representations, lexical multisets of 399 and 199 matching lines, 32 reading passages, eight new external originals and three selective PDF texts. Exact finite diagnostics passed 27 posterior kernels, 480 hybrid event/order/rate cases, 65 parameter instances, three calibration identities and 378 prefix-policy instances. All four permitted live ledgers had drifted, and their original snapshots still matched. Validation attempts and any failures are retained in `validation-history.jsonl`; no failure is erased or converted to a pass. The final inventory replay is separate from this preseal core statement.

No substantial count change, human-review claim, worldwide-priority claim, proof-assistant claim or universal-proof/contribution certification follows from source-hash replay. Parent integration and all independent review gates remain separate.
