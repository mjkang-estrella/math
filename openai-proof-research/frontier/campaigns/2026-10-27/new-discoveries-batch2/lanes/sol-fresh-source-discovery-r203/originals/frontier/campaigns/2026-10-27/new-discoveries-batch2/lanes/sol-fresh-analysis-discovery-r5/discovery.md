# No completed discovery: Krasniqi endpoint-asymptotics question

Research date: 2026-10-29 UTC (2026-10-28 America/Los_Angeles). Solo lane.
No acceptance, discovery credit, paper, or formal endpoint is proposed.

## Selected complete source question and eligibility limits

Primary: Valmir Krasniqi, *On the Alzer–Berg problem: an optimal Bernstein
boundary and a uniqueness conjecture*, arXiv:2609.28707v1, submitted
2026-09-23 18:42:32 UTC. Actual HTML body read: Proposition 3, coefficient
identities (3.16)–(3.19), Lemma 5, Theorem 17, Proposition 21, and Section 9.
Section 9 question (2) asks for endpoint asymptotics of both A(b) and t_b
as b approaches 0 and -1, including the correction to the sufficient line.
This entire question is the target; this lane does **not** substitute a
single fixed parameter, an interior subinterval, or a new wording.

For a>0, 0<=c<1, H_(a,c)(y)=(1+1/y)^(ay-c), and
A(b)=sup{a>0:H_(a,-b) is Bernstein}. The source proves the supremum is
attained, A(b)->0 as b decreases to -1, and the regularized density
Phi_(a,c)(t)=exp(a-t)D_(a,c)(t) is nonnegative at the boundary and has
positive contacts. Let t_b be the unique positive contact as in the public
counterpart described below; alternatively all compact-escape statements
here apply to any chosen contact and require no uniqueness assumption.

The full endpoint question was not found answered in the bounded current
registry/source-body screen. This is a research lead, **not** a worldwide
unresolved-status or novelty certificate. It was not in the inspected
accepted families or prior screen reports. Complete eligibility for a future
result still requires broader primary/citing literature and substantive review.

## Deduplication that changed the selection

1. Wu–Yu–Guo arXiv:2312.01819v4 Conjecture 1, equation (19), asks for all
   derivative signs for Tsallis orders 1<alpha<2 along heat flow. Its actual
   body says this implies the Shannon completely monotone conjecture.
   Gu–Sellke arXiv:2605.11656v1 Theorem 1 and Proposition 1 already give an
   explicit finite Gaussian-mixture counterexample on R. Their H is
   integral p log p, the **negative** of Shannon entropy, so H^(5)>0 is the
   wrong sign. Time normalization by a factor two does not repair it.
   Consequently a near-alpha=1 transfer cannot be credited here. This was
   a preliminary screen, not the selected unresolved target.
2. Krasniqi Conjecture 23 itself is already covered by trureturing's actual
   current `docs/develop/theory/KrasniqiBoundaryContact.md`, Theorem 3.1:
   every -1<b<0 has exactly one positive contact and it is quadratic. The
   whole body, including the rational-partition proof, was read for scope.
   It was posted by commit b297c2a7ac79ad16248db7e30bbcd133d78979fe,
   2026-10-03T22:45:27Z, before this research. No independent kernel replay
   or audit of that public proof is claimed. Exclusion does not require us
   to certify it. Neither its uniqueness proof nor its analytic-continuation
   corollary is a new result in this lane.
3. The exact source's **separate endpoint question** is absent from that
   public proof's conclusions. Its sections 1–3 prove a lower bound and
   interior contact, and section 4 supplies a finite partition, not endpoint
   asymptotics. We therefore pursued that question instead.

The docs-body hit matters: Problems/D5/Blueprint path searches alone did not
find it. The screen was expanded to the complete untruncated docs and Library
subtrees, and the relevant current body was fetched. See provenance.json.

## Validated reduction at the singular endpoint

Write delta=1-c=1+b. The analytic extension at a=0,c=1 satisfies
Phi_(0,1)(t)=exp(-t). Define its first variations by

    U(t)=partial_a Phi_(a,1)(t)|_(a=0),
    V(t)=partial_delta Phi_(0,1-delta)(t)|_(delta=0).

Then, for t>=0,

    U(t)=integral_0^1 [exp(-t)-s^2 exp(-st)]/(1-s) ds,
    V(t)=integral_0^1 [s exp(-st)-exp(-t)]/(1-s) ds.

These are convergent integrals; their numerators vanish at s=1. Here is
an ordinary derivation, independently checked by exact rational identities.
For y>0, L(t)=log(1+1/y)=integral_0^1 1/(y+s) ds. Differentiating
exp(a)-H_(a,c)(y) at (0,1) gives Laplace transforms

    Laplace[U](y)=1-y^2/(y+1) log(1+1/y),
    Laplace[V](y)=-y/(y+1) log(1+1/y).

Partial fractions inside the s integral give precisely the two formulas.
One can also identify them without differentiating an inverse transform:
the source generating function is

    sum q_n z^n = exp(a[-log(1-z)/z-1]-c log(1-z)).

At (0,1), q_n=1. Its parameter derivatives give

    U^(n)(0)=(-1)^n H_(n+2),
    V^(n)(0)=(-1)^(n+1) H_(n+1),

where H_j=sum_(k=1)^j 1/k. Expanding the displayed integrals gives the
same coefficients. Locally uniform exponential-series convergence identifies
the entire functions. This proves the first-variation formulas, not an
asymptotic theorem at moving t.

The particularly useful exact cancellation is

    U+U'=-I_2,    V+V'=I_1,
    I_j(t)=integral_0^1 s^j exp(-st) ds.

Thus a positive tangency of the **linearized model**

    M_(a,delta)(t)=exp(-t)+a U(t)+delta V(t)

must satisfy

    a/delta=I_1(t)/I_2(t).

This is an exact necessary equation for that model, not for the true density.
For t>0,

    I_1=[1-(1+t)exp(-t)]/t^2,
    I_2=[2-(t^2+2t+2)exp(-t)]/t^3.

Elementary Laplace-endpoint expansion gives

    U=-2/t^3-6/t^4+O(t^-5),
    V=1/t^2+2/t^3+O(t^-4).

For clarity, split the integrals at s=1/2. On the first half expand
1/(1-s), with a bounded geometric remainder, and integrate s^j exp(-st).
On the second half the canceled quotients are bounded by a polynomial in t
times exp(-t/2), by the mean value theorem. This justifies these expansions
for U,V, including their displayed error orders.

Consequently any model tangency with t->infinity satisfies

    a/delta ~ t/2,   exp(-t) ~ delta/t^3.

The resulting **unproved true-boundary prediction**, with L=log(1/delta), is

    t_(-1+delta)=L+3 log L+o(1),
    A(-1+delta)=delta/2 [L+3 log L+o(1)].

Do not cite those two formulas as established. Even the leading equivalence
A~delta log(1/delta)/2 is not proved here.

One unconditional but routine reduction is that all boundary contacts escape
to infinity as b decreases to -1. Indeed, source Theorem 17 gives A(b)->0.
For any r<1 the q generating function is bounded uniformly on |z|=r in a
compact parameter neighborhood of (0,1). Cauchy's coefficient bound gives
|q_n|<=C r^-n. The series
Phi=exp(a) sum_n (-t)^n q_(n+1)/n! therefore converges locally uniformly
in parameters and t to exp(-t). On every compact t interval the latter has
a strictly positive minimum. Contacts eventually leave each compact interval.
This is not nominated as a new theorem or a complete answer to question (2).

## Diagnostics and strongest objection

`exact_check.py` uses Fraction arithmetic to verify the differentiated
recurrence through n=40 and filtered coefficients through n=38. `check.py`
checks symbolic partial fractions and generating coefficients and solves
three deterministic floating-point tangencies at delta=10^-2,10^-4,10^-6.
The 200-term results were reevaluated with 260 terms at 70 decimal digits.
No random search was used. Both processes cap address space at 512 MiB.
These tangencies are **not certified boundary points**: neither global
nonnegativity nor interval root isolation nor a truncation remainder was
proved. Their role is to catch a wrong coefficient or sign in the proposed
scale; they provide no proof or acceptance evidence.

Strongest objection: a first-order Taylor expansion valid on compact t
sets cannot be evaluated at t~log(1/delta) without a uniform remainder.
The source's fixed-parameter tail theorem is also not uniform at c=1,
where its leading coefficient vanishes. Higher parameter derivatives,
endpoint singularities, and competing exponential contributions may change
the balance. Tiny numerical residuals do not address this objection.

Precise remaining work: prove bounds on R=Phi-exp(-t)-aU-deltaV and
R+R_t, uniformly for a=O(delta log(1/delta)) and the moving contact window,
small relative to delta/t^3 in both R and R+R_t (a stronger target than
needed for leading equivalences, to retain the proposed additive o(1)); establish global
positivity/exclusion estimates identifying that window and the actual
supremum A; then treat the other endpoint b increasing to 0. No complete
ordinary result exists yet, so no formalization was attempted and there is
no PROOF.md.
