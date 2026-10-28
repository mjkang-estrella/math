# Exact Debye reduction: exclude from discovery credit

28 October 2026. This supersedes the substantive HOLD in REVIEW-ADOPTION.md.
The ordinary proof and preliminary mathematical review remain valid. The
candidate receives **credit 0 as a routine classical corollary**. This is not a
claim that an earlier paper printed Conjectures 5.1–5.2 in resolved form.

## The actual published dependency

NIST DLMF §10.41(ii), equation (10.41.3), gives, as positive real ν tends to
infinity,

    I_ν(νz) ~ exp(νη(z)) / (sqrt(2πν)(1+z²)^(1/4))

**uniformly for every 0<z<∞**. The uniformity statement follows equations
(10.41.3)–(10.41.6) in the actual body. Equations (10.41.7)–(10.41.9) define

    η(z) = sqrt(1+z²) + log(z/(1+sqrt(1+z²))),
    U_0 = 1.

Primary source: https://dlmf.nist.gov/10.41#ii (archived HTML and extracted
text in sources/; read directly). DLMF attributes this expansion and its error
bounds to Olver, *Asymptotics and Special Functions*, pp.374–378. I have not
read those book pages independently. The displayed uniform asymptotic itself
is sufficient: eventually, simultaneously for every positive z,

    1/2 ≤ I_ν(νz) sqrt(2πν)(1+z²)^(1/4) exp(-νη(z)) ≤ 2.       (D)

No new Bessel bound is required. In particular, a nonuniform fixed-argument
large-order formula is not being used.

## Complete bridge, including both tails

Fix **any** p>0 and set ν=n/2 and a=2+1/p. Under r=νz the literal source
integral is

    F_(n,p) = ν^(aν) (2πν)^(1/(2p)) J_ν,

where (D) sandwiches J_ν between 2^(-1/p) and 2^(1/p) times

    L_ν = ∫_0^∞ w(z) exp(νH(z)) dz,
    w(z) = (1+z²)^(1/(4p))/z,
    H(z) = a log z - η(z)/p.

Since η'(z)=sqrt(1+z²)/z,

    H'(z) = (2+1/p-sqrt(1+z²)/p)/z.

Consequently H increases up to its unique maximum at

    z_* = 2 sqrt(p(1+p)),   sqrt(1+z_*²)=2p+1.

Write h=H(z_*). Direct substitution gives

    h = (2+1/p)log 2 + log p + (1+1/p)log(1+p) - 2 - 1/p.   (H)

There is no unproved tail interchange. The following *exact* identity gives
an integrable global envelope for both tails:

    w(z) exp(H(z))
      = z (1+z²)^(1/(4p)) (1+sqrt(1+z²))^(1/p)
          exp(-sqrt(1+z²)/p).                              (E)

For 0<z≤1 its right side is bounded by a p-dependent constant times z. For
z≥1, use sqrt(1+z²)≥z, (1+z²)≤2z² and
1+sqrt(1+z²)≤(1+sqrt 2)z. It is bounded by a constant times
z^(1+3/(2p)) exp(-z/p). Thus C_p=∫w exp(H) is finite and positive.
For ν≥1, H≤h therefore implies

    L_ν ≤ C_p exp((ν-1)h).                                (U)

For a matching lower bound, H is C¹ on [z_*,z_*+1], so its derivative has a
finite absolute bound M_p there; w has a positive minimum c_p there. On
[z_*,z_*+1/ν], H≥h-M_p/ν, giving

    L_ν ≥ c_p exp(νh-M_p)/ν.                              (L)

Equations (D), (U), and (L) prove

    log F_(n,p) = aν log ν + νh + O_p(log ν).

Using (H), this is exactly

    log F_(n,p)
      = n[(1+1/(2p))log n -1-1/(2p)
           +(1/2)log p +(1/2)(1+1/p)log(1+p)] + O_p(log n).

Exponentiating proves the literal Conjecture 5.2, with the same stronger
polynomial-error precision as the elementary candidate. The source's
Corollary 3.8 prefactor

    nπ^n / [2^(n/(2p)) p^n Γ(1+n/2)^(2+1/p)]

and Stirling's formula then give Conjecture 5.1 with precisely the stated
constant [2π sqrt((1+p)^((1+p)/p)/p)]^n, up to exp(o(n)). The preliminary
review independently checked that prefactor against the literal definition.

## Why the preliminary eligibility defense does not survive

The problem fixes p before n tends to infinity. Although z_* tends to zero
when p tends to zero, no simultaneous p-uniform limit is requested. More
strongly, the actual classical expansion is already uniform on the *entire*
positive z-axis, so even the proposed global-tail obstruction disappears.
The remaining argument above is ordinary one-dimensional Laplace bounding,
with an exact integrable envelope and one compact interval. It requires no
new Bessel identity or estimate. The authors' and thesis's p=1 stopping point
is historical evidence, not an obstruction to this explicit classical bridge.

Accordingly no full Lean investment, manuscript, discovery packet or credit
is justified under this campaign's routine-corollary exclusion. The original
ordinary proof, actual-source findings and review evidence are preserved.
All classical tools and the p=1 case are uncredited. Accepted count remains
2/30 additional, 32/60 total. No claim of worldwide priority and no external
posting or problem-status change is made.
