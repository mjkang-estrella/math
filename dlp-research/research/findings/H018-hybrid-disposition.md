# H018 hybrid report: corrections before any experiment

Status: paper review completed, no verified improvement. Raw Grok report
retained separately; completed task suffix
`ecdloop-h018-fullsolver-hybrids-grok-20261008-r1`, full ID in the H018 brief.
Root read task_status, no pending child runs. Native Sol
`/root/h010_early_dependencies` independently reviewed cards1/3; root reviewed
cards2/4 and has supplied the arithmetic identity below for independent check.
No numerical runs, costs calibrated to hardware or new Lean claims.

## Rational-fibre obstruction: true degree identity, false general conclusions

For nonconstant rational f of degree d, composition with [n] has degree n²d.
Consequently an identity f([n]P+T)=f(P) for n≠0 forces |n|=1. This is a
function-field statement, not a classification of all finite-group branch rules.
A nonzero difference has at most d(n²+1) zeros. Positive density only forces
identity when the number of agreements exceeds that bound; n or d growing
with q can make the proposed density obstruction vacuous.

Translation-invariant rational functions need not be constant globally. For a
point T of order q, f(P)=x([q]P+S), for a fixed rational nonzero S, is a
nonconstant rational function invariant under translation by T. On a FULL
order-q rational group it takes the constant value x(S), which is a different
statement. More generally, a nonconstant function invariant under the order-q
translation subgroup has degree divisible by q (the subgroup acts on the
function-field extension over f). Thus a bounded degree below q is excluded,
but the raw unqualified global-constancy assertion is false.

For n=-1, translated reflections remain possible; the quotient need not be
literally x(P) in the chosen origin. Known extra automorphisms, when applicable,
must stay in the baseline. Their rational-group scalar action does not make
them the same function-field morphism as multiplication by a large integer.

The assertion that an affine label relation is the ONLY constant-work recovery
form is unproved. A bounded-degree polynomial in tracked scalar coefficients
could also be useful if actually derived and solved. No such new relation is
supplied, but neither coefficient diffusion nor a degree identity excludes it.
The degree screen is retained; the broad label/recovery obstruction is rejected.

## AP Semaev factor base: unknown logs are missing from recovery

Substituting X=u+iδ and Y=u+jδ into S3(X,Y,x(R)) produces a bidegree(2,2)
polynomial with coefficientδ^4 on i²j². This algebraic observation is correct.
But choosing x-coordinates in an arithmetic progression does NOT give known
logs for the resulting points Pi. The relation with R=Q-aG yields

    signed log_G(Pi) + signed log_G(Pj) + signed(k-a) = 0.

A nonzero coefficient of k does not eliminate the other unknown logs. One
relation is not scalar recovery. Precomputing those logs, or collecting enough
independent relations and solving a system including them, needs its own paid
algorithm, rank/success argument and memory ledger. Choosing known-log points
instead would lose the asserted AP x-coordinate structure unless constructed.

The one-variable Coppersmith p^(1/4) guarantee does not automatically apply to
this bivariate modular equation, and is not a lower bound on all algorithms.
No applicable bivariate extraction theorem was read/established in the raw
report; a mandatory nine-dimensional lattice also does not follow merely from
the polynomial support. The stated field-operation/rho-addition comparison
mixes cost units. These are unaccepted premises, not a rejected new theorem.

A sumset of L admissible factor-base points contains at most O(L²) signed
two-sums, so fixed-trial coverage can give a necessary q/L² scale for constant
success on a uniform target. It does not supply an upper bound or an expected
hitting law for consecutive translated trials. Correlation and actual distinct
sumset size still matter. This route overlaps earlier summation-polynomial
factor-base ideas and currently lacks a complete recovery operation. No lattice
or curve experiment is justified by the presented card.

## Side images: corrected conditional duty-cycle calculation

Root observed that storing BOTH ordinary and doubled keys gives two directed
cross-channels per sample pair, not the one used in the raw duty-cycle formula.
Under the ideal iid model, if each extra doubling image is admitted independently
with probabilityδ, the expected pair rate is proportional to1+2δ. Doubled-
doubled equality repeats the ordinary channel. Exact stopping laws, actual walk
correlation, label usefulness and complete storage costs need their own scope.

Root also supplied the exact shared-arithmetic identity: if
z=(x-xJ)^(-1), λ=(y-yJ)z and xplus=x(P+J) are already available, set
t=(2yJ)z. Then x(P-J)=xplus+t(2λ+t). Precomputing2yJ yields two additional
multiplications plus additions, with no new square or point doubling. Sol
independently checked this identity. Exceptional x=xJ and all precompute/key/
label costs remain. Shared P±J arithmetic is known; it is not a new discovery.
This piecewise reverse-image map is not automatically an injective doubling
map, and adjacent equal jumps can create a constructed return. Its useful
collision law cannot be imported from the ideal doubling calculation.

Sol independently confirmed the exact iid per-pair rate (1+2δ)/N for N=(q-1)/2,
q>5, with independent marks. Under an ADDITIONAL birthday stopping model,
the cost ratio is (1+cδ)/sqrt(1+2δ). For0<c<1 it is minimized at
δ=min(1,1/c-1); for c≥1 there is no saving. The raw c≥1/2 rejection is false.
At c=.8 and δ=.25, the ratio is sqrt(.96), about.9798. Thus the stated
unshared arithmetic ledger admits at most about2.02% saving in that ideal
model, before paid hashes/keys/labels/storage and any actual-walk corrections.
This is NOT a verified complete-work improvement, rho constant or new method.
Both lookup orientations must actually be detected. Ordinary distinguished
endpoints cannot be assumed to reveal these non-coalescing collisions.

## Differential recurrence: paired-state size is not the detection requirement

For Pn=P(n-1)+P(n-2), the known difference P(n-1)-P(n-2)=P(n-3) is indeed
carried. A collision of individual stored points, with useful affine labels,
can recover a scalar; matching the full paired state is unnecessary. Therefore
q² possible paired states do not imply q samples for every detector. Conversely,
the recurrence is invertible and deterministic, not an iid sampler; repeated
coefficient vectors can produce tautologies. No useful first-hit law or complete
storage/restart/cycle schedule is supplied. No numerical test is admitted.

Sol inspected the primary [short-Weierstrass XZ EFD page](https://www.hyperelliptic.org/EFD/g1p/auto-shortw-xz.html),
subsequently opened by root. Differential addition exists in this model; its
listed general7M+2S and mixed6M+2S formulas have additional parameter work and
assumptions. Their existence refutes unavailability, without showing a cheaper
matched full solver. Full odd prime curve order excludes rational2-torsion and
hence base-field Montgomery/twisted-Edwards models. A prime-order SUBGROUP in
an even-cofactor ambient curve does not imply that exclusion. Rational4-torsion
is not necessary for the twisted-Edwards obstruction.

## Verdict and source limitation

No new main-goal gain. The report's claimed closures depend on missing channels,
overbroad morphism claims, an unnecessary paired-state collision requirement,
and missing factor-base logs. These objections are preserved explicitly, not
converted into universal impossibility claims. Initial source use was limited
to snippets/abstracts and existing records; no new small-root theorem was
verified. Reopening requires an actual useful-hit/recovery operation and a
complete cost case, not another invocation of these invalid screens.
