# W019-C twist-product review

Review date: 2026-10-08 America/Los_Angeles; sources and the certificate were
retrieved 2026-10-09 UTC. Role: independent review child. The parent remains
principal researcher. Scope is section C only. Sections A and B of the frozen
hypothesis were read and are not judged here.

Disposition: **reject the twist-product strategy as a factoring improvement.
Accept its Euler cancellation as an exact local identity, and accept the
stated search model only as a heuristic cost account of this losing
strategy.** Verified new end-to-end factoring improvement: **NONE**.

The product-search model is not a theorem and not a lower bound. No explicit
norm, transfer, or relative-class-number map was found that replaces the
product by a low-height integer annihilator while keeping the same
cancellation. The failed representation is the constant function on the twist
group.

The frozen hypothesis [W019.md](W019-twist-product-review-evidence/inputs/research/hypotheses/W019.md)
has SHA-256
`a40930d9f1f38ac00873bb9f41d64d62bd9cf6c586baef194632444c60f222e3`.
The [brief](W019-twist-product-review-evidence/brief.txt), input snapshots,
primary PDFs, and the one class-number certificate are in the
[evidence directory](W019-twist-product-review-evidence/).
`delivery-manifest.json` hashes the delivered payload, including this report.
`delivery-manifest.sha256` is the separate anchor.

## Decisions

1. **Accepted, exact:** away from ramified primes, a genuine group of T
   distinct quadratic twists replaces the paired Euler factor by
   `(1-χ(ℓ)/ℓ)^{-T}` on a thin set and by `(1-ℓ^{-2})^{-T/2}` elsewhere.
2. **Accepted as Dirichlet's theorem, for a fixed twist modulus:** the thin
   set has density `1/T`. This is character orthogonality plus primes in
   arithmetic progressions. It is not a random-sign hypothesis.
3. **Accepted inside the random-sign model only:** the log of the product has
   variance coefficient T, while the log of the geometric mean has variance
   coefficient `1/T`. The coefficient T is amplitude T times density `1/T`.
4. **Rejected as a tail theorem:** `sqrt(T/B)` is not Schoof's GRH bound and
   is not an unconditional enclosure. Schoof's uniform bound, multiplied
   across T characters, is a larger relative error and still loses.
5. **Accepted as a heuristic cost account, for fixed T and fixed conductors:**
   product height `N^{T/2}` times priced multipliers; interval search
   `N^{T/4} B^{-1/4}` times parameter factors; relaxed balance `N^{T/5}`.
   For every fixed T>1 this is worse than the same account at T=1.
6. **Rejected:** the geometric mean, and the integers next to it, as a common
   annihilator. Certificate: class numbers 3 and 2, product 6, nearest
   integer 2.
7. **No extraction map found.** Kuroda's identity and the multiquadratic
   formula rewrite the same large product using a unit index. They do not
   produce a searchable integer of height `N^{1/2}`.

No factoring screen was run. The single preregistered class-number
evaluation exited 0 on its first execution. No trial was discarded and the
code was not edited after the freeze. No delegation, installation, commit,
or shared solver, Lean, STATE, registry, or task-file edit was made.

## 1. Exact local cancellation

Let Ψ be a group of T=`2^r` distinct Dirichlet characters of exponent
dividing 2, including the trivial character. Let χ be one further quadratic
character. For a prime ℓ that divides none of the conductors, every value
ψ(ℓ) lies in `{±1}`, and `ψ ↦ ψ(ℓ)` is a group homomorphism Ψ → `{±1}`.

The image is either `{1}` or all of `{±1}`. In the first case every local
factor equals `(1-χ(ℓ)ℓ^{-s})^{-1}`, so the product is
`(1-χ(ℓ)ℓ^{-s})^{-T}`. In the second case the kernel has index 2. Pairing
the factors gives

    (1 - χ(ℓ)ℓ^{-s})^{-T/2} (1 + χ(ℓ)ℓ^{-s})^{-T/2}
        = (1 - ℓ^{-2s})^{-T/2},

because χ(ℓ)^2=1. At s=1 the first-order logarithm is `T χ(ℓ)/ℓ` on the
thin set and `0` off it. The parent’s pair, T=2, is the same identity:
`(1-ℓ^{-2})^{-1}` when ψ(ℓ)=-1, and `(1-χ(ℓ)/ℓ)^{-2}` when ψ(ℓ)=1.

This is finite group arithmetic. It does not use equidistribution, GRH, or
a class number.

### Exceptions that change the factor

Ramification. If χ(ℓ)=0, then χψ(ℓ)=0 as well whenever ψ(ℓ) is defined and
nonzero, so both displayed factors are 1. The identity
`(1-ℓ^{-2})^{-1}` requires χ(ℓ)≠0. If some ψ is ramified at ℓ, that factor
is 1 rather than a ±1 twist. For a fixed public twist modulus there are
finitely many such primes. Each contributes an explicit bounded factor.
They must be written into the product directly.

Repeated characters. If the proposed T multipliers do not give T distinct
primitive characters, the identity uses the image group. Its order, not the
nominal multiplier count, is the amplitude and the denominator of the
density. Twisting by a square does not add a character.

Nonfundamental and square conductors. For a fundamental discriminant Δ and
a positive integer f,

    χ_{Δ f^2}(n) = χ_Δ(n) if gcd(n,f)=1, and 0 otherwise.

The Euler product therefore drops the primes dividing f. If every such
prime is at most B, the finite products and the full L-values change by the
same known rational factor, so their normalized tails agree. This is the
same exact correlation already recorded for W017. Averaging those
conductors does not sample independent tails. The argument here is the
character identity; W017’s batch-cost and Fourier-comparator conclusions
are not reused.

Valid negative discriminants. χ_d is odd exactly when d<0. If χ is odd and
one public twist ψ is also odd, then χψ is even and its field is real.
Section 4 prices the regulator in that case. A packet of T imaginary
quadratic orders requires every public twist to be even: positive
fundamental discriminants, coprime to the base discriminant or with the
shared primes removed and the resulting characters checked for repeats.

Coprime conductor multiplication. Fundamental discriminants are the
squarefree integers congruent to 1 mod 4, and four times the squarefree
integers congruent to 2 or 3 mod 4. Two coprime ones cannot both be even.
Their product is again fundamental, and the Kronecker symbol is
multiplicative in the upper argument, so the product character has
conductor equal to the product of the conductors. If
`|Δ_ε| = |Δ| ∏_i q_i^{ε_i}` over ε in `{0,1}^r`, each q_i occurs in half of
the T subsets. Therefore

    ∏_ε sqrt(|Δ_ε|) = |Δ|^{T/2} ∏_i q_i^{T/4}.

Shared primes can only replace this by a smaller conductor or a repeated
character. The displayed product is the multiplier that has to be paid when
the twists are genuinely independent.

## 2. Density is a theorem; the variance coefficient is a model

For n coprime to the twist modulus M, the indicator that every ψ(n)=1 is

    (1/T) ∑_{ψ in Ψ} ψ(n).

The sum is T on the kernel and 0 on every other value in `{±1}^r`. If the
chosen fundamental discriminants are independent in `Q^*/(Q^*)^2`, no
nonempty product is a square, the characters are F2-independent, and the
joint map `(Z/MZ)* → {±1}^r` is surjective. The kernel is a union of
exactly `φ(M)/T` residue classes.

Dirichlet’s theorem on primes in arithmetic progressions then gives those
primes Dirichlet density `1/T`. The theorem is used here as a classical
citation and is not reproved. No error term is claimed. For a fixed modulus,
the stronger prime-number theorem in arithmetic progressions would upgrade
the density to the tail comparison
`∑_{special ℓ>B} 1/ℓ^2 ~ (1/T) ∑_{ℓ>B} 1/ℓ^2`; that upgrade is also not
proved here. If M grows with N, this review claims no uniformity down to the
computational cutoff B. The parent’s density `1/T` is the Dirichlet density
when the twists are a fixed independent group, not an equidistribution
heuristic about the unknown character χ.

The variance model adds a second hypothesis: on the special primes, the
unknown character χ behaves like an independent fair sign. That hypothesis
is false as a literal description. χ is periodic modulo its conductor. It
is the random-sign model, and it is separate from the exact cancellation.

Let τ be the tail, above B, of the sum over ψ of
`-log(1-χψ(ℓ)/ℓ)`. Off the special set the inner sum equals
`-(T/2) log(1-ℓ^{-2})`, which is deterministic. On the special set it
equals `-T log(1-χ(ℓ)/ℓ)`, whose leading random piece is `T χ(ℓ)/ℓ`.
Hence

    Var(τ) ~ ∑_{special ℓ>B} T^2 / ℓ^2.

Inside the model, the special primes are given density `1/T` in the
convergent series `∑ 1/ℓ^2`. That series, taken over all primes above B,
has scale `1/(B log B)`. Therefore

    Var(τ) ~ T / (B log B).

The coefficient in front of `∑_{ℓ>B} 1/ℓ^2` is T^2 times density `1/T`,
which is T. A model that kept amplitude 1 on a set of density `1/T` would
have coefficient `1/T`. The parent’s refusal of that coefficient is the
correct arithmetic inside this model. The logarithm of the geometric mean
is τ/T, so its variance has coefficient `1/T`.

The standard deviation of τ has scale `sqrt(T/(B log B))`. The parent’s
relative error `sqrt(T/B)` is the explicit relaxation of that scale, with
the slow logarithm absorbed. This review accepts `sqrt(T/B)` only with that
meaning. It is a model width, not an enclosure that has been proved for
every discriminant.

## 3. What the GRH bound actually supplies

Schoof, Theorem 6.3, assumes GRH and states absolute effective constants
c2, c3 such that for every quadratic-order discriminant Δ and every
`x > c2 log^2|Δ|`,

    |1 - ∏_{p>x} (1 - (Δ/p)/p)| < c3 log(|Δ| x) / sqrt(x).

The statement was read from printed p. 267. The proof begins by assuming a
fundamental discriminant and expressing a weighted prime-power sum as a
contour integral of `L'/L`. That argument and its later extension to
nonfundamental discriminants were not reproved. Lagarias–Montgomery–Odlyzko,
cited for the companion Theorem 6.1, was not opened.

For one L-value, write `L = E_x / P` with
`P = ∏_{p>x} (1-χ(p)/p)`. The displayed bound is `|1-P|<ρ`. When ρ<1/2 this
is a relative error O(ρ) between L and its partial Euler product. For T
characters, the product of the tail factors lies between `(1-ρ)^T` and
`(1+ρ)^T` only after imposing the hypothesis of Theorem 6.3 on every
discriminant in the packet, including the largest conductor. The resulting
relative error has size about `T log(N M B)/sqrt(B)` while that quantity is
small. This deduction does not reuse cancellation between the characters.
A uniform product bound on the heuristic scale `sqrt(T/B)` is not stated in
the pages read, and it is not proved here.

Both widths lose to one character once they are multiplied by the height in
the next section. The sharper model is not required for the rejection, and
the larger GRH consequence is not an unconditional theorem.

## 4. Height, units, and the relaxed balance

For an imaginary quadratic order, Schoof’s displayed formula on printed
p. 245 is

    h = w(O) sqrt(|Δ|) / (2π) * L(1, χ),

also for non-maximal orders, with w(O) the number of roots of unity in the
order. For Δ not equal to -3 or -4, and w=2, this is
`sqrt(|Δ|)/π * L(1,χ)`. The citation for the general abelian formula (4)
on printed p. 244 is Lang, which was not opened. The shape used here is the
shape printed by Schoof:

    h = w sqrt(|Δ|) / (2^{r1} (2π)^{r2} R) * ∏_{χ ≠ 1} L(1, χ).

For an imaginary quadratic field, r1=0, r2=1 and the regulator contribution
is absent from the reduced formula, in agreement with the conventional
regulator 1 of a unit-rank-zero field. The exceptional unit counts w=4 and
w=6 occur for the orders of discriminants -4 and -3. In a general packet,
`w_ψ` divides 6 and contributes at most a factor `6^T` to the product.
For fixed T that factor is constant. It has to appear in an exact identity,
and it does not change the power of N.

A positive discriminant has r1=2 and r2=0, so formula (4) puts the
regulator in the denominator. The class number is then
`sqrt(Δ) L(1,χ) / (2R)`, not the imaginary expression
`sqrt(Δ) L(1,χ) / π`. An odd public twist produces this real field. Its
regulator is a further unknown real number. The imaginary product model
does not apply to that factor until the regulator is computed and removed.
That computation is not priced by an Euler product alone.

For T even twists of a negative discriminant of size Θ(N), the coprime
conductor calculation of section 1 gives

    H = ∏_ψ h_ψ
      = N^{T/2} * ∏_i q_i^{T/4} * ∏_ψ (w_ψ/(2π)) L(1, χψ),

up to the constant hidden by writing the base discriminant as Θ(N). The
partial Euler product that approximates `∏ L` is computable and becomes the
center of the interval. After the first-order cancellation, its typical
size is polylogarithmic in the cutoff for fixed T. The parent’s phrase
“scale `N^{T/2}`, up to discriminant multipliers and L-values” is the
correct description of this center. It is not a proved lower bound that
every such product exceeds `N^{T/2}`.

By Lagrange’s theorem, H annihilates every element of every constituent
form class group: the group order divides H, and the exponent divides the
group order. Each separate class number already annihilates its own group.
The product is a common multiple, not a shorter one.

Grant the model’s relative error `ρ = sqrt(T/B)`. The absolute interval
containing H then has width `ρ` times the center. A baby-step/giant-step
search in one of the class groups costs

    N^{T/4} B^{-1/4} T^{1/4} ∏_i q_i^{T/8}

group operations, times the square root of the explicitly computed
unit and partial-L factors. Each group operation is composition and
reduction at discriminant size `N ∏ q_i`, with bit cost polynomial in
`log(N ∏ q_i)`. Schoof describes those operations as elementary; this
review does not assign a sharper multiplication exponent. The parent’s
count `N^{T/4} B^{-1/4}`, with parameter factors, matches this group
operation count.

Balance that search against a cutoff stage of cost proportional to B, for
fixed T and fixed q_i. Then `B^{5/4}` has scale `N^{T/4}`, so
`B` and the balanced cost have scale `N^{T/5}`. At T=1 this is the familiar
model scale. At T=2 the same relaxation balances at `N^{2/5}`.

The GRH union width replaces `sqrt(T/B)` by `T log(NMB)/sqrt(B)`. The
balanced cutoff remains a constant power of T, times logarithms, times
`N^{T/5}`. For every fixed integer T>1, both relaxations are worse than
the T=1 account. Making one twist conductor a positive power of N inserts
the extra search factor `q^{T/8}` and must be charged, as the parent
required.

These comparisons are costs of specified workloads inside specified error
models. They do not lower-bound other algorithms, and they do not prove
that a uniform machine must run for `N^{T/5}` steps. Schoof’s own
comparator, read from printed pp. 264–265, is the GRH-conditional
class-group search that produces an ambiguous form and factors N in time
`N^{1/5+ε}`. Its proof was not re-audited. It remains the T=1 reference
against which this product is more expensive in the relaxed model.

One further obligation survives even after H is known. An annihilator of
one sampled class yields a nontrivial involution only when that class has
even order, and the involution factors N only when its ambiguous form meets
the factor identities Schoof prints on p. 265. The Euler-product
calculation does not supply the sample or that success event.

## 5. The geometric mean is not an annihilator

The normalized geometric mean has the better variance coefficient `1/T`,
and its archimedean size is about `N^{1/2}` times fixed-twist factors. It
is not in general an integer. Raising a class to a non-integral power is
not a group operation.

The finite maximal-order formula printed by Schoof on p. 245,

    h = 1/(2-χ(2)) * ∑_{0<x<|Δ|/2, gcd(x,Δ)=1} χ(x),

was evaluated once under the preregistration in the evidence directory.
The frozen program returned h(-23)=3 and h(-115)=2. Both groups therefore
have prime order, so they are cyclic and a positive integer annihilates
both if and only if it is a multiple of 6. The product 6 does. The
geometric mean is `sqrt(6)`, and the nearest integer is 2. The element of
order 3 satisfies `g^2 ≠ 1`. The integer 3 likewise fails to annihilate the
group of order 2. Borevich–Shafarevich, Schoof’s reference for this finite
formula, was not opened; the arithmetic uses the formula as printed, with
the Kronecker values fixed in the preregistration.

The same integers agree with the reduced primitive forms under the counting
rule stated on printed p. 246, `|b|≤a≤c`, together with the boundary sign
used in Schoof’s discriminant -691 example. They are `(1,1,6)`, `(2,±1,3)`
for -23, and `(1,1,29)`, `(5,5,7)` for -115. The bijection between reduced
forms and classes was not reproved.

The pair is a genuine twist packet. The characters are χ_{-23} and
χ_{-23}χ_5 = χ_{-115}, both odd, with even public twist χ_5. Their Euler
factors cancel exactly off the primes with `(5/ℓ)=1`. The integer that
inherits the cancellation is the product 6, whose size is already the
entire common annihilator. Nothing near the geometric mean works.

## 6. Norms and relative class numbers keep the large integer

Lemmermeyer, printed pp. 246–247, defines the ideal-extension map

    j : Cl(k1) × Cl(k2) × Cl(k3) → Cl(K)

for a V4-extension and states

    h(K) = 2^{d-κ-2-v} q(K) h1 h2 h3 / h_k^2,

where `q(K)=(E_K : E1 E2 E3)` is the unit index. Over Q, with K imaginary,
the printed special case is

    h(K) = (1/2) q(K) h1 h2 h3.

For a negative discriminant twisted by one positive discriminant, the three
quadratic fields are the two imaginary fields and one real field. The
product of the two imaginary class numbers is therefore

    2 h(K) / (q(K) h_real).

The real class number is public when the twist is a fixed public
discriminant, and computing it is a separate priced class-group
computation. The unit index q(K) remains. Benjamin, Lemmermeyer, and Snyder,
printed pp. 27–28, record the multiquadratic extension: if `[L:Q]=2^m`,
then

    h(L) = 2^{-ν} q(L/Q) ∏_i h(k_i),

with the product over all `2^m-1` quadratic subfields and

    ν = (m-1)(2^{m-2}-1) + 2^{m-1}-1

when L is complex. They state that q is the obstruction, that there is no
explicit formula for q in general even in degree 4, and that Wada’s unit
algorithm is the available computation. Wada’s paper was not read. The
displayed examples on those pages already take q through `2^7`, so q is not
a universal constant absorbed for free when the degree grows.

For the field generated by one negative discriminant and r independent
positive ones, m=r+1 and the quadratic subfields consist of the T imaginary
twist fields together with T-1 real fields. The formula recovers
`∏ h(Δ_ψ)` only after multiplying by `2^ν / q` and dividing by the real
class numbers. Those real class numbers and the unit index are extra
computations. They cancel constant factors for fixed twists; they do not
replace `N^{T/2}` by `N^{1/2}`.

The kernel and cokernel of j explain the ratio of these class numbers.
Lemmermeyer also records that quadratic classes can capitulate in K, so the
quadratic class groups do not automatically embed into Cl(K). That is an
obstruction to transporting relations downward for free. It is not an
algorithm which, given truncated Euler products, returns a short
annihilator of Cl(Δ). Calling the kernel an oracle would rename the missing
map. No costed computation of that kind is supplied by the identity.

The group-ring calculation closes the linear possibilities. For coefficients
e_ψ, the first-order coefficient at an unramified prime ℓ is

    χ(ℓ)/ℓ * ∑_{ψ in Ψ} e_ψ ψ(ℓ).

As ℓ runs through primes, ψ ↦ ψ(ℓ) runs through all homomorphisms Ψ → `{±1}`
once the twist characters are independent and Dirichlet’s theorem is
granted. The sum vanishes on every nontrivial homomorphism if and only if
every e_ψ is equal. Every linear combination that preserves the full
cancellation is therefore a scalar multiple of the product of the L-values,
and the corresponding integer is a power of the product of the class
numbers times the explicit unit and archimedean factors above. That integer
has the model height `N^{T/2}` times the conductor multipliers.

## 7. Boundaries and the next question

W017 was read in full. Its finite batch and equal-input Fourier comparator
are outside this scope. Its square-conductor tail identity is the character
identity in section 1, re-proved here. No tail or extraction gain is added.

W004’s frozen hypothesis was read through its field-law selector, lines
1–80 of 168. A search of the rest found no class-number, Euler-product, or
annihilator hypothesis. Its object is a pair of modular norm equations in a
root fiber. Those conclusions are not used.

The exact failed representation is the constant vector `(e_ψ)`. It is the
unique linear form, up to a scalar, that keeps the first-order cancellation
at every unramified non-special prime, and the integer it produces is the
product of the class numbers up to the priced factors in sections 4 and 6.

The next mathematical question is narrower. Is there an explicit function,
not a fixed linear combination of the class numbers, which takes the public
twists and the truncated Euler products and returns a proved multiple of
the exponent of one imaginary-quadratic class group of discriminant Θ(N),
at height `N^{1/2+o(1)}`, with every unit, regulator, conductor, and
class-group operation in an extension of degree greater than 2 either
absent or charged, and with an error law that is either unconditional or
explicitly GRH-qualified? The identities read here do not provide one.

A positive answer would need a new map and a new error statement. Another
evaluation of a small class-number product, or another average of square
conductors, would not.

## Read boundary

Exact pages, unread proofs, and the certificate freeze are in
[read-scope.md](W019-twist-product-review-evidence/read-scope.md).
The local Euler and group-ring arguments, the conductor-product arithmetic,
and the relaxed exponent comparisons are proved in this review. Every
class-number identity quoted from Schoof, Lemmermeyer, or
Benjamin–Lemmermeyer–Snyder is a displayed statement whose proof was not
reproduced.
