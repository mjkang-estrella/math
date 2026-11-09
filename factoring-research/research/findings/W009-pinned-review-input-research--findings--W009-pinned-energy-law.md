# W009 — the acquired involution is biased by its actual merger mass

2026-10-08. Parent derivation, PROVISIONAL pending independent audit.
No candidate run, solver/Lean edit, or improved factoring bound.
This supplies the exact symbolic gate from [W009](../hypotheses/W009.md).

## Legal triples and rejected mass

Fix one odd prime and the current projective output law mu on P^1(F_p).
Write z=mu(0), h=mu(infinity), and nu for mu restricted to F_p^*, with
zero mass at both marked atoms. Set s=sum nu, v=sum nu^2, u=sum nu^3,
q4=sum nu^4 and q5=sum nu^5.

The local legal event is exactly that three independent draws a,y,w are
distinct nonzero finite values. The N-only implementation checks the
denominators and a,y,w,y-w, then 1+a*t, where t=(a-y-w)/(y*w).
Since 1+a*t=(a-y)*(a-w)/(y*w), the unit chart has precisely this local
meaning. Its probability is

    ell=s^3-3*s*v+2*u.                                  (1)

For a fixed map modulo N=pq, fresh CRT samples give joint clean-chart
probability ell_p*ell_q. This is NOT a success probability, and conditioning
on clean charts is not free. Every unsuccessful draw has already paid for
three circuit evaluations. A proper gcd is an early factor; a full-gcd
failure is retained. A stage retry policy must explicitly pay for retries
or cap them, and prior survived histories need their actual joint law.

## Pointwise residual update, with BOTH marked atoms removed

For a legal triple let iota(z)=(a-z)/(1+t*z) and b=iota(infinity).
Thus b=-1/t if t!=0, otherwise b=infinity; define nu(b)=0 in the latter
case. If b is finite then it is distinct from 0,a,y,w. The map
F(z)=z(z-a)/(1+t*z) has iota-orbits as its fibers.

Define the nonzero off-diagonal pairing mass

    Pi_(a,t)=sum_(z in F_p^*, iota(z) in F_p^*, z!=iota(z))
                         nu(z)*nu(iota(z)).

The two marked masses change by

    z_new=z+nu(a),  h_new=h+nu(b).

The full collision change includes the cross terms 2*z*nu(a) and
2*h*nu(b). Subtracting the changes in the SQUARES of both marked atoms
cancels those terms and leaves the exact identity

    v_new-v=Pi_(a,t)-nu(a)^2-nu(b)^2.                   (2)

Fixed points are excluded from Pi, not counted as newly merged pairs.
The planted pair y,w contributes exactly 2*nu(y)*nu(w) to Pi.

## Reindexing the ACTUAL sampler, rather than assuming a useful oracle

For fixed nonzero a and t with 1+a*t!=0, the ordered legal pairs y,w
which produce t are exactly the off-diagonal pairs w=iota(y) in the
sum defining Pi. Therefore the unnormalized probability of acquiring
this involution is

    nu(a)*Pi_(a,t),   and sum_(a,t) nu(a)*Pi_(a,t)=ell.   (3)

The sampler automatically biases toward involutions with more current
merger mass. It never measures Pi or receives it as advice. Consequently

    ell * E[v_new-v | legal]
      =sum_(a,t) nu(a)*Pi_(a,t)
                  *[Pi_(a,t)-nu(a)^2-nu(b)^2].          (4)

This is the candidate computational advantage made precise: the positive
term uses the SQUARE of merger mass. It is not a proof that this term
dominates absorption, or that a favorable law can be acquired cheaply.

The two absorption laws are also explicit. Writing G_0 and G_infinity
for their unnormalized expected increments,

    G_0=(s^2-v)*v-2*s*u+2*q4,
    G_infinity=sum_(a,t) nu(a)*Pi_(a,t)*nu(b).           (5)

The zero-atom square-removal contribution in (4) alone is
(s^2-v)*u-2*s*q4+2*q5. No zero/full-gcd event may be counted as a new
factor merely because these masses increase.

## Multiplicative coordinates and the pinned-energy computation

For fixed a use x=1-a/z. This sends a to 0, infinity to 1, and
conjugates iota to x -> delta/x, with delta=1+a*t !=0. Define

    rho_a(x)=nu(a/(1-x)) for x in F_p^* with x!=1,
    rho_a(1)=0.

Then

    Pi_a(delta)=sum_(x*y=delta, x!=y) rho_a(x)*rho_a(y),
    nu(b)=rho_a(delta),
    ell=sum_(a,delta) nu(a)*Pi_a(delta).                (6)

Equation (4) is thus a weighted multiplicative-energy statistic of
Möbius-transformed residual laws, with the diagonal removed. For an
unweighted support S, put B={1/z:z in S}. Up to a nonzero scalar, the
transformed support is B-1/a, with its zero removed. The positive
numerator is a pinned sum of shifted multiplicative energies. This
connection may permit a real incidence bound or a correlated construction;
no such theorem has yet been imported.

Primary leads found, not yet accepted as applicable theorems:
Shkredov's author bibliography and papers on shifted multiplicative
subgroups; Macourt--Shkredov--Shparlinski on shifted-subgroup energy.
Any field-size restriction, flat-weight assumption and subgroup promise
must be checked before using them for an adaptive output law. The parent
has only inspected search/author-list material so far.

## Two cheap exact controls, neither a factoring experiment

For a flat residual law nu=s/m on a support of size m>=3, every legal
update has Pi>=2*s^2/m^2 from its planted pair, and both removal terms
are at most s^2/m^2. Hence v_new>=v pointwise. This is a restricted
positive invariant absent from the arbitrary-law polynomial update.
It says nothing about how the post-update law ceases to be flat, or how
quickly roots/poles are acquired at paid cost.

For a residual support consisting of exactly three distinct nonzero
points with masses alpha,beta,gamma, every legal triple uses all three.
Its conditional anchor a is uniform over the THREE LABELS, despite their
unequal masses; the probability of each ordered triple is alpha*beta*gamma.
The pole b is outside this support, and the only residual paired orbit
is the other two support points. Thus

    ell=6*alpha*beta*gamma,
    E[v_new-v | legal]=(s^2-2*v)/3,
    E[z_new-z | legal]=s/3.

For example over F_7, masses (5/7,1/7,1/7) on {1,2,3} give
ell=30/343 and residual drift -5/147. This is an exact distribution
counterexample to universal nonnegative drift, not a demonstrated
reachable tower state. It does not refute improvement through immediate
absorption: roots increase even while residual mass decreases.

## Next actual work

Audit (1)-(6), including multiplicities, poles and clean-chart probabilities.
Then either derive a uniform bound on the positive pinned energy under
REACHABLE laws, or supply a paid generator of a law for which large
pairing overlap survives repeated updates. A subgroup-shaped starting
support alone is insufficient: its transform is a shifted reciprocal
subgroup, whose multiplicative energy can be much smaller. The sampler
and the coordinate change are explicit; persistence and total cost remain
the unsolved bottleneck. Keep the independent scalar-product branch active.
