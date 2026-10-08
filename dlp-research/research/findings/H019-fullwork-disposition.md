# H019 collision schedules: corrections and matched-baseline screen

2026-10-08. Verified improvement **NONE**. No numerical experiment admitted.
Raw Grok report: H019-fullwork-grok-raw.md. Native Astra
/root/h007_additive_relations independently reviewed card1; native Sol
/root/h010_early_dependencies reviewed cards2–4. Both completed. Root checked
the elementary identities and inequalities. Raw blanket closures are not
accepted. The separate high-memory baseline calculation is recorded in
H019-xonly-baseline-screen.md. These are paper reviews, not Lean proofs.

## 1. Chord bonus

For x(P)!=x(J), with lambda=(y(P)-y(J))/(x(P)-x(J)) and
t=2y(J)/(x(P)-x(J)),

    x(P-J)=x(P+J)+t*(2*lambda+t).

Given the ordinary-addition intermediates and precomputed 2y(J), this costs
2M plus additions. Equal-x dispatch remains paid. With s=S/M in [0,1], extra
cost c=2/(5+s) lies in [1/3,2/5], not at most 1/3. A bonus point carries
labels (a_P-a_J,b_P-b_J). An x-only match leaves a sign ambiguity; recover it
or verify both candidate scalars. Zero unknown coefficients, scalar arithmetic,
storage, hashing, replay and failed checks are not free.

Write W_t=e_t*(W_(t-1)+J_t), e_t in {±1}, B_t=W_(t-1)-J_t.
An automatic return is B_t=e_(t-1)*W_(t-2) when
J_t=e_(t-1)*J_(t-1). Merely repeating the oriented index does not suffice
when the preceding sign is negative. A universal probability 1/r needs an
actual partition, sign, mixing and cycle-handling model.

The exact cross equations are

    B_t=eta*W_s  iff W_(t-1)-eta*W_s=J_t,
    B_t=eta*B_s  iff W_(t-1)-eta*W_(s-1)=J_t-eta*J_s.

The second is not automatically an ordinary collision. For instance two
predecessors A+J_i and A+J_j can have the same bonus A without being equal
up to sign. Conversely a deterministic bonus map duplicates ordinary
collisions, so independence of all channels is also unjustified.

Ordinary endpoint coalescence does not discover every side collision. A common
coordinate-based distinguished predicate CAN directly capture equal side keys
if both record types are stored and compared. Under an additional uniform-key
model, density theta thins that common event by theta, not theta². Constant
strength then needs constant density and square-root-scale records in that
model. This is not a universal memory lower bound for all discovery schedules.

Let F denote the actual useful-collision enhancement and h extra bookkeeping
in ordinary-addition units. The conditional ratio is (1+c+h)/sqrt(F).
F=2 gives .943–.990 before overhead, whereas F=3 gives .770–.808.
Neither F is proved. The raw .95 ceiling and rejection of a third channel were
unsupported. A 10% gain over that rho comparator needs
F>((1+c+h)/.9)^2, plus all setup/failure costs. More importantly, the high-memory
case must also beat the stronger BSGS comparator; the F=3 arithmetic case does
not. See the separate baseline screen for assumptions and remaining scope.

## 2. Fibonacci stream

P_n=P_(n-1)+P_(n-2) has difference P_(n-3). For P_n=e*P_m,

    (b_n-e*b_m)k=e*a_m-a_n.

The raw negative-sign recovery formula was wrong. In units M, the general
differential core ratio (7+2s)/(5+s) is 1.4–1.5, not at least 1.5.
The [primary EFD](https://www.hyperelliptic.org/EFD/g1p/auto-shortw-xz.html)
lists additional parameter products and additions. Its mixed formula requires
a normalized difference, not a fixed jump. Running differences can be normalized
and retained, at charged cost. Constant jump does not itself make P-J constant.
Affine lookup normalization is also paid.

An invertible pair-state recurrence does not exclude single-point collisions.
Uniform marginals do not establish a first-hit law. A theta^-1/2 storage
penalty needs a specified iid sampling/retention model, not merely this
recurrence. Two general labelled seeds require four scalar multiplications or
two explicitly priced multiscalar routines. Cheaper seeds change assumptions.
No supported stopping-time/work gain or universal rejection is established.

## 3. Isogenous models

Fp-isogenous elliptic curves have exactly equal rational point counts:
an isogeny intertwines Frobenius and induces an isomorphism of rational Tate
modules, preserving its characteristic polynomial. Consequently an entire
odd-prime-order rational group has no rational 2-torsion anywhere in its
Fp-isogeny class, precluding Montgomery/twisted-Edwards rational models there.
This statement is about the FULL rational group, not a prime subgroup of an
even-cofactor group. The raw q>4sqrt(p) condition is unnecessary.

Degree>=q is not a runtime exclusion: multiplication maps may have compact
evaluation. If phi(G)!=O, known scalar labels transport directly; no inverse
point map is needed. If phi(G)=O, the whole prime-order subgroup is killed.
Neither point-count invariance nor degree rules out all isogeny algorithms.

## 4. Residue filtering

The conditional birthday gain criterion is c*sqrt(delta)<1, equivalently
c<1/sqrt(delta), not c<sqrt(delta). Finite fixed-jump lists need not be
independent; a fallback can leave the filtered subset. The raw density-only
birthday estimate therefore does not describe that actual walk.

A useful scoped calculation DOES close ideal capped rejection with fresh iid
uniform proposals, accepting the first member of a density-delta set and
otherwise returning the last proposal after r>=1 trials. Put f=(1-delta)^r.
Expected trial count c=(1-f)/delta; output masses on the set/complement are
1-f and f, uniform within each. Relative pair-collision intensity is

    u=(1-f)^2/delta+f²/(1-delta).

Then c²>=u iff f<=1-delta, which holds for every r>=1 (strict when r>1,
0<delta<1). Thus this ideal model loses addition-only birthday work before
paying predicate tests. It is not a stopping-time theorem for a deterministic
filtered EC walk. Density estimates alone do not prove independence or useful
label collisions. Unverified tag-tracing constants were not accepted.

## Admission

The raw report identified no supported new complete-work gain, but several
purported universal obstructions were false. Keep the corrected conditional
screens; do not infer all four mechanism families impossible. A new run needs
a specific surviving mechanism, success/discovery model and matched resource
baseline. No GPU throughput or large-curve timing was measured here.
