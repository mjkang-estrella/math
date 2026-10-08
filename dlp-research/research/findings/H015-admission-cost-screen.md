# H015 uniform-root comparator sharply limits admission-only gains

2026-10-08. Root proposed the stronger comparator and work argument; native
Astra /root/h007_additive_relations independently verified both in a NEW review.
Native Sol /root/h010_early_dependencies separately assessed the experiment-value
gate. Paper result only, no Lean claim, experiment or complete-solver improvement.

## Collision count with a competent baseline

Use the same signed-forest/endpoint process as H015-component-admission.md.
Choose uniformly among R currently unresolved ROOTS, not original targets or
already-solved components. Conditional on retained endpoints T with actual
endpoint subprobability law nu, useful probability per start is

    nu(T) - nu(T_unknown)/(2R) >= (1-1/(2R))*nu(T).

Equivalently, each encountered endpoint collision reduces R with probability
at least p_R=1-1/(2R). No uniform-basin assumption enters. This remains true
conditional on the entire infinite geometric seed-path stream and past label
history: (a,sigma)<->(n=a+sigma*d_r,sigma) preserves uniform product measure,
so choosing a uniform seed point does not reveal the independent fair sign.
The stored endpoint's owner is already fixed by past history; a uniformly chosen
root hits that owner with probability at most1/R. Each useful event removes
one unknown root variable, so K reductions are needed.

For a continued uncapped process with eventual collisions, completion collision
count N is conditionally stochastically dominated by

    S = sum(R=1..K) Geom(1-1/(2R)),
    E S = K + H_odd(K),
    H_odd(K) = sum(R=1..K) 1/(2R-1) = H_(2K)-H_K/2 = O(log K).

Geom counts the successful trial. Independence is used for the DOMINATING
geometric variables, not falsely assumed of actual useful events. This bound
holds conditional on geometry; S's law is independent of that geometry.
Every admission policy in this recovery model needs at least K collisions.
Thus no such policy can promise a fixed asymptotic fraction of saved collision
events against this comparator. This is not an ECDLP lower bound generally.

## When it transfers to starts and common geometric work

Require iid root-independent seed paths, unchanged walk/cutoff INSIDE each path,
first-record retention independent of labels, no table eviction or attempt caps,
and finite expected waiting. A path may fail its fixed internal cutoff; its
cost and failure are charged. Initially K unknown variables remain after all
supplied relations. Only specified collision information is used for recovery.

Let n_j be the number of starts through collision j and g(j)=E n_j, g(0)=0.
For T subset T', couple identical future paths: the next repeat against the
growing table initialized with T' occurs no later than for T. Hence expected
next-repeat waiting h(T) is decreasing under set inclusion. Tables at successive
collisions grow, so g(j+1)-g(j) is nonincreasing. The piecewise-linear extension
of g is concave. Conditional domination followed by Jensen gives

    E n_N <= E g(S) <= g(E S)
          <= (1+H_odd(K)/K)*g(K).

All competing admission policies require at least the first K collisions in
the common geometric stream. Thus uniform-root expected START overhead is at
most O(log K/K) relative to that absolute benchmark. The same argument applies
to accumulated nonnegative, root-independent per-path work, even when cost is
correlated with the path's endpoint: a larger retained table stops earlier on
the coupled stream. Alternatively a common conditional expected per-start charge
allows Wald. No measured group-operation constant or runtime is inferred.

Root-dependent seed implementation, variable forest/scheduler work, final
verification and physical batching need separate accounting. Fixed-base seed
work can sometimes be included through its common conditional expectation;
this requires an actual implementation/cost convention. Do not silently assume
that every scalar multiplication has the same complete cost.

## Important cap and memory limits

This is NOT a bound for the frozen16K-start/4K-record repeated attempt. A deadline
allowing only about K collisions can distinguish policies, and conditioning on
success changes the work distribution. Equal hard memory budgets cannot be
replaced by an unlimited baseline table. Expected independent repeated-attempt
cost is w/p (mean attempt cost w, success probability p), including setup again.
For a10% gain, p_candidate/p_uniform must be at least
(10/9)*(w_candidate/w_uniform). Neither quantity is established. Compare optimized
baseline caps and paid preprocessing/reuse, not just an arbitrary unfavorable cap.

The earlier stopped Chernoff statement is also scoped correctly:
P(4K collisions reached before caps AND fewer than K reductions)<=exp(-K/4).
It is a JOINT event, not a conditional bound given cap survival. Reviewer expressly
confirmed root's qualification.

## Independent experiment-value review

Small fixed K is not rejected by this asymptotic screen. When W~sqrt(q/K) is
large, scalar seeds, scheduling and verification might be small relative to
walk work. But the proposal has supplied no favorable complete ledger. The
R=1 admission ACTION is identical for all policies; its incoming state/mass
distribution need not be identical, which complicates per-phase comparisons.

Sol offered an explicitly hypothetical K3 price envelope: uniform phase charges
(6/5+4/3+2)C=68C/15 versus ideal(1+1+2)C=4C, with common overhead S0 and extra
selector cost H. A10% saving would require H+S0/10<=2C/25. This grants equal
collision prices, near-unit unknown mass and negligible selected-root mass at
both earlier stages. It is NOT a construction of two actual coupled executions,
nor evidence the mass assumptions are compatible across their phases. Root
retains this limitation: solving a heavy component changes later known-anchor
mass, so immediate usefulness cannot alone predict total savings.

## Exact two-root cancellation with a fixed table

Root proposed this separate check; Astra independently simplified both formulas.
Normalize the distribution conditional on an endpoint collision. A frozen table
has known mass w0 and unknown-root masses x,y, with w0+x+y=1. Every observation
is a repeat in this deliberately restricted model. No new records are inserted.
Signs are independent and fair. Let V(m)=1/(1-m/2), the expected collisions
needed to solve one remaining root of mass m. Choosing root i gives self-failure
w_i/2, self/known resolution w0+w_i/2, or merge w_j. Hence

    E_i = [1+(w0+w_i/2)*V(w_j)+w_j*V(w_i+w_j)]/(1-w_i/2).

Put s=x+y, p=xy. Both choices simplify to

    E_1=E_2=2*(8-6s+s^2+2p)/((2-x)*(2-y)*(2-s)).

The equality is stronger than an expectation coincidence. With
V_m(z)=z*(1-m/2)/(1-z*m/2), both action generating functions are

    F(z)=z^2*(C-z*D)/[(1-z*x/2)*(1-z*y/2)*(1-z*s/2)],
    C=1-s/2-p/4,
    D=s*(2-s)/4-p*(4-s)/8.

Substitution satisfies BOTH action Bellman equations. On a redundant self-hit
the state stays fixed; on a useful event only one root remains. Induction on
the collision deadline therefore shows that every nonanticipating adaptive
root-choice policy has the SAME completion collision-count distribution. This
includes fixed COLLISION-count deadlines in this model. No measurements or
computer algebra were used. This is not a growing-table, path-time, K>2 or
variable-implementation-cost theorem.

Interpretation: choosing a heavy component risks more redundant self-hits, but
successfully solving it creates more known-anchor mass for the next stage.
Maximizing immediate rank reduction ignores that compensating transition.
The K3 envelope above cannot be treated as an attainable gain without these
state distributions.

## Three-root fixed-table expectation also cancels

A separate native Astra /root/h006_structured_relation_ideas checked the next
Bellman equation by hand. Write F(a,b)=E_2(a,b), with the useful decomposition

    F(a,b)=2/(2-a)+2/(2-b)+4*a*b/[(2-a)*(2-b)*(2-a-b)].

For masses x,y,z>=0 with S=x+y+z<=1, define
t=2-S, h=x-y, U=2-x, V=2-y, W=2-z,
A=2-y-z, B=2-x-z, C=2-x-y,
c_x=2-2S+x, c_y=2-2S+y. Solving the self-failure recurrence gives

    E_(3,x)=[2+c_x*F(y,z)+2y*F(x+y,z)+2z*F(x+z,y)]/U.

Subtract the y-action expression. The cross-multiplied numerator is

    N=U*V*(E_(3,x)-E_(3,y))
     =2h+V*c_x*F(y,z)-U*c_y*F(x,z)-2h*C*F(x+y,z)
       +2z*[V*F(x+z,y)-U*F(y+z,x)]
     =2h*[-4z/t+4z*(W*t+x*y)/(t*A*B)] = 0,

because A*B=(W-y)*(W-x)=W*t+x*y. All denominators are positive on this domain;
there is no division by h or a mass. Permutation proves equality of all three
action expectations, including zero/equal masses. The recurrence's useful-event
continuations use the already policy-independent two-root expectation. A finite
expected stopping argument therefore also allows nonanticipating root choices.

This removes the optimistic fixed-table K3 expected-collision motivation, rather
than asserting the two policies share the same terminal-state distribution.
No K3 completion-distribution identity, all-K theorem, growing-table result or
path-time cap conclusion is claimed. Root checked the Bellman coefficients and
factor identity; this remains a paper derivation with no Lean/Audit entry.

Disposition: park implementation/diagnostic until a concrete finite-K weighted
cost or capped-success mechanism supplies a favorable case against the stronger
baselines. No generic functional-graph engine justified. The exact fixed-table
K2 calculation further narrows the toy motivation without extrapolation to
growing tables or all ECDLP.
