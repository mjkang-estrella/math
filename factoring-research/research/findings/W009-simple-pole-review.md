# W009 simple-pole persistence: independent review

2026-10-08. **Disposition: accept equations (1)-(7) for the stated unpowered
two-anchor protocol, with the scope and powered-map qualifications below.**
No algebraic repair to those seven equations is required. The second-step
asymptotic and the every-history character bound are valid. The full-tape
argument supplies an unconditional success upper bound for a fixed raw-attempt
budget and specified gcd channels. It supplies no actual-work lower bound,
no conclusion at greater depths, and no general factoring lower bound.
Verified new factoring complexity improvement: **NONE**.

The powered-map paragraph is valid as a one-step spectral decomposition when
its measure is explicitly restricted to nonzero finite outputs. Its exceptional
coefficients equal the residual mass `s`, not `1`. The contribution
`g*s^4/(p-1)` is exact, but it is not necessarily the dominant contribution.
A precise remainder bound is given below. Repeated powered folds are outside
the accepted recurrence.

This review concerns the new persistence derivation. It does not repeat the
three-anchor audit or the separate flat-subgroup calculation. The two-anchor
local drift identity is checked only as a dependency of the persistence proof.
No candidate, numerical sweep, solver change, Lean change, package installation,
commit, publication, shared-state write, or recursive delegation occurred.

## Frozen record and primary theorem

The input manifest freezes the five requested project instructions/contracts,
`research/STATE.md`, the W009 hypothesis for context, both mathematical parent
briefs, and the pinned Kowalski source and its existing extraction. The review
brief preserves both mathematical originals. All review-created files have the
`research/findings/W009-simple-pole-review` prefix. This review did not edit
originals. A delivery check observed concurrent changes to `research/STATE.md`
and the live two-anchor note; this audit remains pinned to the frozen versions.
The parent persistence note was unchanged at that check. The delivery manifest
records the observations without adopting concurrent edits as reviewed inputs.

The audited parent persistence file has SHA-256
`ce5abe608e3c069267179e27fa4246c3ca7f1ede49d1ff1e04d7d4963d5e5da1`.
The two-anchor dependency has SHA-256
`1770e04c695cd246935b30a437a470c4046e65c9ec2593952613642214d5547b`.

I independently opened the [primary PDF](https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf#page=33),
downloaded it, compared it byte-for-byte with the pinned copy, extracted PDF
page 33, and inspected that page's rendering. Both PDFs are 715170 bytes with
SHA-256 `ff30b82d143cedcaf76f1ef2f15a49856c0eabc2c95ba7ac0da2e3e43da9a866`.
The version is September 14, 2021; Theorem 3.1 is on printed page 31.

Theorem 3.1 applies to a multiplicative character of order `d>1`, with
`d | q-1`, and a polynomial `G` over `F_q` which is not a `d`-th power over
the algebraic closure. If `G` has `rho` distinct geometric zeros, its complete
character sum has magnitude at most `(rho-1)*sqrt(q)`. The theorem does not
require squarefreeness or degree below `q`. The adjacent degree restriction
belongs to the additive-character theorem, not to Theorem 3.1.

All applications below use that theorem only after exhibiting a non-power
certificate. Character values at zero are zero; the rational-map sums also
exclude poles. The exponent introduced to encode a character or denominator
does not multiply the number of distinct zeros.

## 1. Exact first trace law and equation (1)

Assume an odd prime `p` and a legal pair `y,w in F_p^*`, `y != w`.
Write `A=y+w`, `c=y*w`, and `Q(b)=(b+A)^2-4c`. A nonzero affine input `x`
has output `b` precisely when

    x^2 - (b+A)*x + c = 0.

Because `c != 0`, every root of this quadratic is nonzero. Thus its number of
roots is exactly `n(b)=1+chi(Q(b))`. The sole affine input at infinity is
`x=0`, so `n(infinity)=1`. At `b=0` the two distinct roots are `y,w`.
These are counts for uniform AFFINE input, with denominator `p`, not `p+1`.

The discriminant of `Q` is `16c != 0`, and `Q(0)=(y-w)^2 != 0`. It has two
distinct nonzero geometric roots. The number of those roots in `F_p` is
`f=1+chi(c)`, which is either zero or two. They give `f` singleton nonzero
output fibers; the number of doubleton nonzero fibers is `(p-3-f)/2`.
Consequently, for every positive integer `r`,

    sum_(b!=0) n(b)^r = 2^(r-1)*(p-3) - (2^(r-1)-1)*f.

In particular all the parent's counts are exact, and the additional moments are

    z0 = 2/p,  h = 1/p,  s = (p-3)/p,
    v  = (2p-6-f)/p^2,
    u3 = (4p-12-3f)/p^3,
    q4 = (8p-24-7f)/p^4,
    ell = s^2-v = (p^2-8p+15+f)/p^2,
    max nu <= 2/p.

The next conditional local expectation exists only when `ell>0`. At `p=3`
there is no residual legal pair. At `p=5`, the case `f=0` also has `ell=0`;
the case `f=2` has positive `ell`. Every legal first pair has positive `ell`
for `p>=7`. These statements follow from the formulas, without a finite-field
enumeration.

For nontrivial `eta=omega^a`, where `omega` has order `p-1` and
`1<=a<=p-2`, character orthogonality gives `sum_(b!=0) eta(b)=0`. Hence

    p*M(eta)
      = sum_(b!=0) chi(Q(b))*eta(b)
      = sum_b omega(b^a * Q(b)^((p-1)/2)).

The last identity also holds at zero, because `a>0`. The polynomial has exactly
three distinct geometric zeros. Its multiplicity at zero is `a`, which is not
divisible by `p-1`; it is therefore not a `(p-1)`-st power over the algebraic
closure. Theorem 3.1 gives `|p*M(eta)|<=2*sqrt(p)`, establishing (1).
This uses the unnormalized residual measure `nu`; normalizing it by `s` would
require dividing the bound by `s` as well.

## 2. Fourier normalization, diagonal removal, and equation (4)

Put `n=p-1` in this section only. With

    M(eta) = sum_b nu(b)*eta(b),
    C(c) = sum_a nu(a)*nu(c/a),
    d(c) = sum_(a^2=c) nu(a)^2,
    Gamma = C-d,

the chosen Fourier transform has no normalization in the forward direction.
Its convolution transform is `M(eta)^2`, and orthogonality yields

    sum_eta |M(eta)|^2 = n*v,
    sum_c C(c)^2 = (1/n)*sum_eta |M(eta)|^4.

The trivial coefficient is `M(1)=s`. If every other coefficient has magnitude
at most `delta`, the nontrivial fourth-power sum is between zero and `delta^2`
times the nontrivial second-power sum. This proves (2), including its factor
`1/(p-1)` and the subtraction `s^2/(p-1)`. That subtraction is nonnegative
after combination with `v`, by Cauchy-Schwarz.

The map `a -> c/a` permutes `F_p^*`, so Cauchy-Schwarz gives `C(c)<=v`.
Also `sum_c d(c)=v` and `0<=Gamma<=C`. Expanding its square gives

    sum Gamma^2 = E_mul - 2*sum C*d + sum d^2,
    E_mul-2*v^2 <= sum Gamma^2 <= E_mul.

This proves (3); it does not incorrectly remove only one diagonal term.

For completeness, the needed local drift dependency follows from the fold's
involution `z -> c/z`. Its nontrivial finite collisions have total ordered mass
`Gamma(c)`, including the planted pair. The atoms at zero and infinity merge
to infinity. Removing the new zero mass squared therefore leaves

    Delta v = Gamma(c) - (nu(y)+nu(w))^2,
    Delta m = nu(y)+nu(w),  m=z0+h.

Weighting by the actual ordered samples `nu(y)*nu(w)`, `y!=w`, gives

    A := sum_(y!=w) nu(y)*nu(w)*Delta v = sum Gamma^2 - B,
    B := sum_(y!=w) nu(y)*nu(w)*(nu(y)+nu(w))^2
       = 2*s*u3 + 2*v^2 - 4*q4 >= 0,
    sum_(y!=w) nu(y)*nu(w)*Delta m = 2*(s*v-u3).

Thus the removal term really is nonnegative for every residual law, not just
for the trace law. This dependency check does not assume subgroup persistence.

For the trace law the preceding bounds give the explicit finite sandwich,
valid whenever `ell>0`,

    [s^4/(p-1) - 2*v^2 - B]/ell
       <= E[Delta v | fixed first map, next local legal pair]
       <= [s^4/(p-1) + (4/p)*(v-s^2/(p-1)) - B]/ell.

Here `v<=2/p`, `u3<=4/p^2`, `q4<=8/p^3`, and `0<=B<=16/p^2`.
Also `s^4/(p-1)=1/p+O(p^-2)` and `ell=1+O(p^-1)`, uniformly in the legal
first pair. It follows that `sum Gamma^2=1/p+O(p^-2)` and that the drift is
`1/p+O(p^-2)`. Adding the exact old `v` proves (4): the next residual collision
mass is `3/p+O(p^-2)`. The second-to-first ratio tends to `3/2`, not `2`.
This is an expectation over the next local legal pair, not a statement about
each next pair, and not an all-depth asymptotic.

## 3. Every legal history, basepoints, and equation (5)

The starting pair `U=X,V=1` is coprime and monic, with degrees `D,D-1` for
`D=1`. Suppose these properties hold over either prime component. Since
`deg U > deg V`, both `U-yV` and `U-wV` are monic of degree `D`. Hence

    U'=(U-yV)*(U-wV),  V'=U*V

are monic of degrees `2D,2D-1`. If `V(alpha)=0`, coprimality gives
`U(alpha)!=0`, and `U'(alpha)=U(alpha)^2!=0`. If `U(alpha)=0`, then
`V(alpha)!=0` and `U'(alpha)=y*w*V(alpha)^2!=0`. Thus `U',V'` have no common
geometric zero. No cancellation changes the displayed degrees.

The degree-two outer homogeneous pair likewise has no basepoint: at `U=0`
its first coordinate is `y*w*V^2`, and at `V=0` it is `U^2`. Infinity maps
to infinity. The degree difference remains exactly one, so infinity has
valuation `-1` as a pole of the rational function. No genericity or finite
squarefreeness hypothesis is needed. A no-op leaves all properties intact.
All globally legal accepted histories therefore have `D=2^a`, where `a` is
their accepted update count; after `j` raw attempts, `D<=2^j`.

These are rational-function polynomials reduced by their common factors;
there is no reduction modulo `X^p-X`. Functional coincidences on `F_p` do not
invalidate the polynomial non-power argument.

For a nontrivial character of order `d>1`, define

    G=U*V^(d-1).

On a finite nonzero output, `eta(G(x))=eta(U(x)/V(x))`. At a root or pole,
`G(x)=0` and its character value is zero; the positive exponent `d-1` is
essential for this pole exclusion. Thus the complete polynomial sum is
exactly `p*M(eta)`, with no omitted-pole correction term.

The polynomial has at most `deg U+deg V=2D-1` distinct geometric zeros and

    deg G = D+(d-1)*(D-1) = d*(D-1)+1.

Its degree is not divisible by `d`, so it cannot be a `d`-th power even over
the algebraic closure. This remains a valid certificate if its degree exceeds
`p`, if some zeros repeat, or if a degree is divisible by the characteristic.
Theorem 3.1 therefore gives `|M(eta)|<=(2D-2)/sqrt(p)`, exactly (5).
At `D=1` the bound is zero, agreeing with the affine identity start. At very
large `D` it may be weaker than `|M|<=s`; validity is not usefulness.

## 4. The composite full-tape process and conditioning

For this part `N=p*q` has distinct odd prime factors. The clean event at a
prime is that both fresh endpoint outputs are finite and nonzero and are
distinct. Its probability is `ell_r=s_r^2-v_r`. Over `Z/NZ`, unit tests of
the two denominators and numerators, followed by the affine difference,
implement the intersection of these two clean events. Endpoint inversion
is used only after the denominators are units; equivalent homogeneous
difference testing has the same local zeros on that chart.

The full-tape process samples two fresh independent uniform residues at every
raw attempt, for a fixed budget `k`. Any nonunit chart gcd, whether proper or
full, gives a no-op in this counterfactual process. Only globally clean pairs
update the map. The real algorithm can stop on a proper gcd. Full gcd failures
remain charged attempts; they are not retried for free.

Conditional on the entire current map modulo `N`, the fresh local sample pairs
are independent by CRT. In particular, conditioning on the other prime's
clean event does not reweight a local legal pair. Multiplying its unnormalized
local drift by the other prime's clean probability gives exactly

    E[Delta v_p | current map] = ell_q*(sum Gamma_p^2-B_p),
    E[Delta m_p | current map] = ell_q*2*(s_p*v_p-u3_p).

These formulas also make sense if either clean probability vanishes; no division
by `ell_p` is needed. The root/pole checks at intermediate circuit stages do
not introduce a stricter clean event: a root or pole cannot later become a
nonzero finite endpoint under this update, as detailed below.

The local map histories are generally correlated because global acceptance
uses both primes. They are not asserted independent, either unconditionally
or on survival. Fresh CRT independence conditional on a fixed past is a
different fact. All expectations in (6) are for the unconditioned full-tape
process; replacing them with expectations conditioned on the real algorithm's
survival would require a new argument. Early stopping is handled by pathwise
coupling, not by treating survived map laws as unconditioned laws.

## 5. Recurrence constants and equation (6)

The factor `ell_q` cannot simply be deleted from a negative drift. The valid
upper-bound chain instead uses the nonnegative positive part first:

    ell_q*(sum Gamma_p^2-B_p)
      <= ell_q*sum Gamma_p^2
      <= sum Gamma_p^2
      <= 1/(p-1) + delta_j^2*v_p,
    delta_j=(2^(j+1)-2)/sqrt(p).

Here (2) and (3) were used along with `s_p<=1` and `D<=2^j`. Also
`0<=s_p*v_p-u3_p<=v_p`. Taking expectations proves the two recurrences in the
parent note. Their initial values are exactly
`v_0=(p-1)/p^2` and `m_0=1/p`.

With `a_i=delta_i^2`, iteration and `v_0<=1/(p-1)` yield

    E[v_j] <= (j+1)/(p-1) * product_(i=0)^(j-1) (1+a_i)
           <= (j+1)/(p-1) * exp(sum_(i=0)^(j-1) a_i),
    sum_(i=0)^(j-1) a_i
      = [(4^(j+1)-4)/3 - 8*(2^j-1) + 4*j]/p
      <= (4^(j+1)-4)/(3*p).

Empty products and sums give the claimed bound also at `j=0`. If `j<=k` and
`4^k<=p`, the last exponent is below `4/3`; `exp(4/3)<4`. Thus

    E[v_j] <= 4*(j+1)/(p-1),
    E[m_j] <= 1/p + 2*sum_(i=0)^(j-1) E[v_i]
            <= 1/p + 4*j*(j+1)/(p-1).

This verifies (6) with the stated indices and constants. The accompanying
symbolic certificate file checks the polynomial identities and the constant
using an exact rational Taylor-tail bound, not floating-point estimates.

## 6. Permitted early factor channels and equation (7)

For a fixed constructed circuit, if an input ever reaches zero or infinity,
the next accepted update sends it to infinity, and subsequent updates keep
it there. No-ops also preserve membership in this union. Consequently every
intermediate numerator or denominator zero during an anchor evaluation
implies that its endpoint is in the current map's root/pole fibers. The same
holds if the two displayed numerator factors are tested individually: their
zeros become roots at that stage. This statement uses the exact valid
projective circuit, without divisions at a pole or artificial coordinate
scalings by nonunits.

Consider raw attempt `j+1` at map index `j`, with `0<=j<k`.
A proper gcd from its literal tests implies at least one of these events at
one prime:

1. One of the two anchor endpoints is zero or infinity.
2. Both endpoints are finite, nonzero, and equal, so the anchor difference
   vanishes there.

The first event has probability at most `2*m_j`; the second has probability
exactly `v_j`. The local upper bound is therefore `2*m_j+v_j`. The two-prime
union bound needs no independence between their current maps. At the first
real proper-gcd event the full-tape map is still identical to the real map,
so this event is included in the corresponding union on the full tape.

For each fresh final probe, any proper factor from separate numerator and
denominator tests implies an endpoint atom at one prime. Intermediate
root/pole tests during that probe are covered as well. Its conditional
probability is at most `m_k,p+m_k,q`. Freshness matters: this statement does
not authorize reusing anchors or searching among conditioned inputs at the
same price. A fixed number `t` of independent fresh probes, or at most `t`
such probes before stopping, is covered.

Using (6) for each `r in {p,q}` gives the training sum

    sum_(j=0)^(k-1) [2/r + (8*j*(j+1)+4*(j+1))/(r-1)]
      = 2*k/r + 2*k*(k+1)*(4*k-1)/(3*(r-1)).

Adding `t` final-probe bounds proves precisely (7), for nonnegative integers
`k,t` and `2^k<=sqrt(min(p,q))`, capped by one. In particular the `k=0`
case includes only the initial root tests on the final probes.

For context, separate numerator/denominator testing has exact fixed-map
success probability `1-r_p*r_q-z_p*z_q-h_p*h_q`, with `r_r=1-z_r-h_r`.
This can benefit from opposite zero/infinity colors, but it is still bounded
by `m_p+m_q` as used here. Intermediate checks can make a successful event
visible even when both final colors agree; the endpoint-atom upper bound
continues to include those events. The bound does not assume that testing
only the final colors has the same success rate as testing intermediate ones.

The theorem excludes extra coefficient tests, sums such as `y+w`, derivatives,
comparisons with retained samples, and other unlisted gcd channels. Adding
one changes the protocol and requires a new success ledger. Preprocessing
successes are likewise outside a statement made for a remaining distinct-odd-
semiprime input. Prime powers and general composites have not been covered.

The strongest compact consequence of (7) is an
`O((k^3+t*k^2+k+t)*(1/p+1/q))` success envelope in its depth range. This is
not an actual-work lower bound. In particular, the nominal accepted-stage
training estimate `O(k^2)` is neither a lower bound on the work of every
raw-budget tape nor a restart theorem. Random accepted depths, charged no-ops,
early stopping, arithmetic widths, and expected restart work need their own
ledger. Nothing from the old polynomial tower's actual-work result is imported.

## 7. Powered-map escape: exact one-step statement and limits

Take a positive integer `e` and a fixed inner map `R=U/V` in the simple-pole
family just verified, evaluated on a fresh uniform affine input. Write its
residual measure as `nu_R`, with mass `s`, second moment `v_R`, and character
transform `M_R`. Let `nu_H` be the residual pushforward under `H=R^e`.
Raising to a positive power preserves zero and infinity and sends each
nonzero finite output to a nonzero finite output; thus the residual mass is
still `s`. For every character, including the trivial one under this residual
convention,

    M_H(eta)=M_R(eta^e).

Put `n=p-1`, `g=gcd(e,n)`, and `K={eta : eta^e=1}`. The character group is
cyclic of order `n`, so `|K|=g`, INCLUDING the trivial character. For `eta in K`,

    eta(R(x)^e)=1 on nonzero finite outputs,
    M_H(eta)=s = 1 - Pr[R(x)=0 or infinity].

This is where root/pole exclusions matter. The unnormalized complete affine
sum is `p*s`, not `p`. One must not apply the polynomial encoding with `d=1`:
then `V^(d-1)=1` would fail to exclude the poles. Separating these `g`
characters exactly avoids both mistakes.

For every other `eta`, the character `psi=eta^e` has order `d'>1`. Applying
the already proved simple-pole certificate to `psi` gives

    |M_H(eta)|=|M_R(psi)| <= delta_R=(2D-2)/sqrt(p),

independently of the integer size of `e`. No extra root/pole error term is
required for this nontrivial sector. The exact energy identity and a useful
finite remainder bound are

    E_H = g*s^4/n + (1/n)*sum_(eta notin K) |M_R(eta^e)|^4,
    0 <= E_H-g*s^4/n
       <= delta_R^2*(v_H-g*s^2/n),
    E_H-g*s^4/n <= ((n-g)/n)*delta_R^4.

Alternatively, since every character in the image of `eta -> eta^e` has `g`
preimages, the remainder is at most
`g*delta_R^2*(v_R-s^2/n)`. These statements specify the parent's phrase
"main energy term": `g*s^4/n` is an exact exceptional-character contribution
and a lower bound, with dominance requiring control of the remainder. It is
not an equality for the whole energy in general. Nor does high `E_H` alone
lower-bound the next drift: diagonal and planted-root removal must still be
included with the new measure.

Projective exponentiation `[U:V] -> [U^e:V^e]` costs `O(log e)` modular
multiplications by binary powering, preserves local validity, and supplies a
real different computation. It leaves current root/pole fibers unchanged, so
it does not by itself improve this same probe's root/pole factor events.
Its possible use is to alter subsequent nonzero collisions and acquisition.
The output lies in the `e`-th-power subgroup of index `g`; a large chosen
integer `e` by itself gives no lower bound on useful `g` for an unknown prime.
The exponent's acquisition, representation, powering, and useful CRT
separation all remain charged obligations.

For `e>1`, an initially simple pole of `R` becomes a pole of order `e` for
`H`. A subsequent unpowered reciprocal fold retains that order, rather than
restoring a simple pole. With a pole order `L`, a valuation certificate would
exclude `d`-th powers only when `d` does not divide `L`; the formerly automatic
certificate for every nontrivial character is lost. Thus the one-step
identity does not close a repeated-powered-fold recurrence. It does not show
that several acquired subgroup constraints persist through translations and
folds, or that useful kernels can be obtained without the usual order-divisor
resource. Taking powers alone is the ordinary cyclic-group compression
mechanism, not a new way to obtain that resource.

## Acceptance, remaining proof question, and delivery

Equations (1)-(7) pass as scoped. No original formula has been overwritten.
The clarifications required for reuse are: residual rather than conditional
normalization; `d>1` in the polynomial spectral argument; unconditioned
full-tape expectations; the specified gcd-channel list and fresh probes;
and a separate exceptional sector and remainder for the one-step powered map.

The useful new conclusion is that this actual reciprocal acquisition rule
has expected residual collision mass `O((j+1)/p)` and expected root/pole mass
`O((j^2+1)/p)` within the stated half-log raw-depth window. These are upper
bounds in expectation, not pointwise persistence laws.
The first trace law fails to keep doubling at the second locally legal step.
No useful all-depth growth or complete factoring improvement is established.

A materially different computation remains open: powered folds with paid
acquisition of useful kernel indices and a proof of the nontrivial spectral
sector after subsequent folds. A decisive next symbolic test would specify
the exponent-selection rule, its cost without hidden prime-order inputs, and
the divisor/character behavior of the next inner map. A separate scalar-product
computation can also avoid this fiber-mass model entirely; this audit places
no lower bound on it. Neither direction is selected for an experiment by these
formulas alone.

Evidence is source inspection plus exact algebra. The companion
`W009-simple-pole-review-symbolic-certificates.json` contains ten passing
formal identities/inequalities checked using Python's standard-library exact
rational arithmetic. They validate arithmetic manipulations, not a candidate
run or a Lean formalization. The delivery manifest lists every artifact and
SHA-256 hash; its checksum file additionally hashes the manifest itself.
