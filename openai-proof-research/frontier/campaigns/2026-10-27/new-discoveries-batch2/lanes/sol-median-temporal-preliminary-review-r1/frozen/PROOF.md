# An averaged-clock finite counterexample to temporal marginal monotonicity

Status: full ordinary-mathematics counterexample, with exhaustive integer certificate. Not accepted, not counted, not formalized. The independently coded forward check is an internal validation by the same solo researcher, not an independent acceptance review.

## Exact source claim and process

Amir–Baldasso–Beilin, *Majority dynamics and the median process: connections, convergence and some new conjectures*, arXiv:1911.08613v2 (2019 submission, v2 dated 2023-01-02), Section 2 PDF pp7–9 and Conjectures 3.1/3.2 PDF p10. On any graph in the well-defined source setting, at each vertex and every iid initial density p≤1/2, the probability of spin 1 is conjectured nonincreasing in time. The source explicitly includes finite graphs. Each vertex has an independent rate-one Poisson clock. An update takes the majority of its neighbors, keeping its own spin on a tie. No conditioning on clock realizations is allowed in the conjecture.

## Witness and conclusion

Let V={0,...,9}. The undirected simple edge set is

```
{1,2}, {0,3}, {1,3}, {2,3}, {3,4},
{0,5}, {2,5}, {3,5}, {1,6}, {2,6}, {4,6},
{5,7}, {0,8}, {3,8}, {4,8}, {5,8},
{1,9}, {5,9}, {7,9}.
```

Set p=2/5 and observe vertex 1. Write m(t)=Pr(spin_1(t)=1). Then

**18/1000000 < m'(8) < 19/1000000.**

Consequently m is not nonincreasing. This refutes the full universal temporal claims 3.1/3.2. It does not refute the separate convexity claims 3.7/3.8. Via the threshold coupling of source Proposition 2.2, the same finite graph refutes 3.1 at alpha=2/5. Continuous initial uniforms cause no threshold atom on a finite graph, since every later opinion is one of ten initial values.

## Generator and preservation of every update order

Identify configurations with integers s=0,...,1023, bit i being the spin at i. Let U_i(s) be the deterministic majority update at i, ties keeping bit i. On functions define

T h(s)=sum_(i=0)^9 h(U_i(s)), Q=T-10 I, f(s)=bit_1(s), g=Qf.

Only updating vertex 1 can change f, so |g|≤1. The initial law is w_s/W, where w_s=2^{|s|}3^{10-|s|} and W=5^{10}. Superposing the ten clocks gives rate 10 and iid uniform vertex labels. Therefore, exactly,

m'(8)=e^(-80)/W sum_(k≥0) (8^k/k!) c_k,
c_k=sum_s w_s (T^k g)(s).

In particular T^k sums all 10^k ordered clock-label words, including ineffective updates. There is no selected schedule or missing exponential holding-time factor. This also follows directly from e^(8Q)=e^(-80)e^(8T).

## Rigorous truncation and finite integer checks

Let K=240, F=240!,

A=sum_(k=0)^240 8^k (240!/k!) c_k,
B=sum_(k=0)^240 80^k (240!/k!),
C=121*80^241, D=19521=241*81.

Every quantity is an explicitly specified integer. Because |T^k g|≤10^k and sum_s w_s=W, |c_k|≤W*10^k. For the exponential tail after term 240, successive ratios are at most 80/242. Thus

sum_(k≥241)80^k/k! ≤ (80^241/241!)/(1-80/242) = C/(D F).

It follows that

(D A-W C)/(W(D B+C)) ≤ m'(8) ≤ (D A+W C)/(W D B).

The following two strict integer inequalities complete the proof:

```
1000000*(D*A-W*C) > 18*W*(D*B+C)
1000000*(D*A+W*C) < 19*W*D*B.
```

`certificate.py` computes U, g and the 241 coefficients using only integer addition, multiplication and rational arithmetic, and asserts both inequalities. `certificate-results.json` supplies every c_k and the actual integers A,B,C,D,W for direct audit. No floating-point operation appears in the certificate. `forward_check.py` independently constructs each update from signed neighbor votes and propagates integer masses forward; at every k it checks c_k = mass_of_ones_after_next_sum - 10*mass_of_ones_before and total mass W*10^k. All 241 coefficients agree. The recorded exact checks pass under the unchanged resource guard.

Finite-state Markov marginals are analytic in t. A positive derivative at t=8 therefore gives an interval of strictly increasing m. This is a full in-scope refutation, rather than an asymptotic heuristic or finite sample of clock orders.

## Strongest classical-adaptation and subsumption objection

Uniformization is a classical identity for finite continuous-time chains. Rational Poisson tails and exhaustive state propagation are standard tools. Nothing here claims a new uniformization method, a new Boolean-function theorem, or a new general invariant. The mathematical content proposed for review is the particular graph's positive *averaged* temporal derivative, which contradicts the explicitly quantified source conjecture.

The source itself gives a K_(3,m) scheduled-update counterexample in Proposition 3.6 (PDF pp11–12). That proof fixes one high-side update, all low-side updates, then the first high-side vertex again. It establishes nonmonotonicity conditioned on one schedule and cannot supply the sign after averaging all schedules. Our graph and the generator certificate must survive that stronger averaging, and do. Source Example 3.9 gives an odd monotone Boolean function with nonconvex biased expectation; it is neither a temporal derivative calculation nor an averaged-clock realization. These are the strongest apparent source shortcuts and neither subsumes this certificate.

Mossel–Neeman–Tamuz arXiv:1207.0893v1 Lemma 5.1, PDF p13, proves the initial-bias bound for monotone balanced Boolean functions using influences and Efron–Stein. That compares a time marginal with its initial value, not two time marginals. Our m'(8)>0 is compatible with m(t)≤p. The two accessed Amir–Baldasso percolation companions concern spatial threshold/crossing events on Z², not a temporal marginal on every finite graph.

An unknown earlier graph counterexample or a general existing theorem implying this one would destroy a novelty claim. The bounded current arXiv searches and actual bodies inspected did not identify one; they do not clear all citing literature, full current public registries or inaccessible historical intervals. Those gaps remain explicit. This lane supplies no worldwide-priority claim. Root must decide significance and commission adversarial review before any acceptance or count. No Lean or manuscript was produced, as instructed.
