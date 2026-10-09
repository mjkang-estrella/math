# H047 sibling-min arithmetic correction and limited dynamics

2026-10-09 UTC. Root derivation, independent native Astra algebra/dynamics and
native Sol complete-cost reviews completed. The user subsequently requested
shutdown after existing work; this preserves the completed review and admits
no experiment. Grok proposal: H047-walk-grok-raw.md. Separate Factory Fable
review completed; its unchecked heuristic conclusions remain separate in
H047-walk-fable-review-raw.md. No new followup review was commissioned.

## Regular arithmetic

For P=(x,y), J=(u,v), u!=x, both finite, set

    d=(u-x)^-1, l=(v-y)*d, t=v*d,
    xp=l²-x-u, xm=xp+4*t*(t-l), lm=l-2*t.

The selected ordinate is l_selected*(x-x_selected)-y. Computing only that
ordinate after comparing xp,xm costs4M+S outside inversion: l,t, correction,
selected ordinate. For K regular denominators the batch costs

    K*(7M+S)+(I-3M).

Additions, small constants, comparisons, signs, canonicalization and all
bookkeeping remain separately charged. Minus occupancy does not affect this
schedule. Computing the plus ordinate eagerly instead pays one more M when
minus wins, not the two in the raw report. The field-only ratio against5M+S
is(7+s)/(5+s), s=S/M, equal4/3 at s=1. A3/4 relative step-count break-even
threshold assumes all other costs and batch remainders match; neither review
establishes that useful stopping time. This is not a novelty or solver claim.

P=O, J=O and x(P)=x(J) require separate paid dispatch. On an odd-order
subgroup regular siblings cannot have equal abscissae: that would give2P=O
or2J=O. No exception is silently charged as an ordinary regular addition.

## What the point-only map actually guarantees

Grok's J0=O makes index-zero states absorbing. Non-DP absorbing states never
trigger its null-replay retirement rule and can consume the cap. Infinity
jump handling is not covered simply by a zero-denominator branch.

If U=g(W) and W,U choose the same nonzero jump, the next candidate classes
include [W], so x(g²(W))<=x(W) on the finite regular domain. Constant-index
stretches have nonincreasing every-other abscissa; changing indices need not.
With one constant nonzero jump the negation-quotient nearest-neighbor graph
is a path with endpoint phenomena, so its minimum-neighbor map has only fixed
points or two-cycles. Ordinary internal backtracking cancels labels; endpoint
self-loops may expose a useful known-multiple relation and are not all null.
These statements are not a useful-collision or DP-discovery law.

## Existing Fable review returned at shutdown

Fable supplies an alternative ordinary affine schedule: compute both slopes
directly with2M, square each with2S, and compute only the chosen ordinate withM.
Root checked this supplied count:3M+2S outside inversion, hence
6M+2S+(I-3M)/K in a regular batch. It is cheaper than the displayed difference-
of-squares schedule when S<M, equal when S=M; neither is asserted optimal.
The field-subtotal ratio is(6+2s)/(5+s), still4/3 when s=1. This does not change
the missing useful stopping premise or constitute a new executable test.

Fable confirms the separate Grok card2 label error: reflection is P->G-P,
so a swapped double has labels(1-2a,-2b), not simply a sign times(2a,2b).
Swapped initialization from Q has(1,-1), not(0,-1). Doubling needs the
deterministic representative chosen by the sorted pair. The rule itself is
already H023's parked alternative; no new mechanism is established.

Do not accept Fable's approximate1/16 absorbing fraction, mean16 trapping,
Theta(1/r) cycle rates, numerical stationary occupation, or IID min-density
"gain ceilings" as actual walker bounds. They require unproved probabilistic
assumptions and do not bound all useful stopping laws. Its statement that no
one-addition selector exists is also unsupported. The root/native statement
is only that no cheaper selector was supplied. These disagreements are retained
without a new review round because the user ordered shutdown.

Coalescence requires one shared global transition seed; per-walker start seeds
must not silently choose different maps. Producing a random start Q+[rho]G
pays for [rho]G as well as the final addition. Charge DP tails/traffic, memory,
replay, coefficient comparison, exact recovery, verification and abandoned work.
A global cap bounds work but does not repair missing success guarantees.

No cheaper exact selector was supplied. Avoiding materialization of both x
values does not by itself eliminate the sibling-correction multiplication.
No impossibility of a cheaper selector is claimed. Correct arithmetic alone
does not justify a diagnostic, a cap reset or a changed baseline. Verified
complete-work improvement remains NONE.
