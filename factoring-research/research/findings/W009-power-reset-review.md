# W009 power reset: independent four-fiber review

2026-10-08. **Disposition: accept the reset theorem and equations (1)–(4).
Accept (5) as a necessary condition with `ell != p`; sharpen its inseparable
interpretation and revise the three-support boundary prose below.** No
counterexample breaks the five equations in their stated prime-to-characteristic
scope. Four distinct simple zero/pole values prevent every prime-to-`p`
perfect power after the inner fold, regardless of earlier powers or wild
ramification. This supplies the certificate missing from the repeated-powered
case of the simple-pole review.

Two wording corrections are needed. Four is the uniform obstruction for all
primes `ell != p`; three already suffice when `ell >= 3`. Also, exactly three
odd-multiplicity divisor support values are impossible: their number must be
even. A rational outer map with three **total** support values can have
two odd ones, which is consistent with a genus-zero square-root cover.

Best supported result: an exact geometric reset and a degree-dependent
spectral upper bound. Verified factoring complexity improvement: **NONE**.
There is no factoring lower bound, success recurrence for arbitrary powered
histories, or acquisition theorem for useful exponents here.

This review uses the accepted reciprocal-law disposition and the simple-pole
review only within their scopes. It does not revive the rejected two-color
impossibility or `1/p^2` alignment assertions, repeat the local moment audit,
or audit the next coalesced-anchor algorithm. Only the stated divisor change
for that next candidate is considered.

## Record and theorem sources

The complete task brief, all thirteen read project/dependency inputs, and the
complete primary source files are frozen under this review's filename prefix.
The audited parent `W009-power-reset.md` has SHA-256
`419b32a0ece616b3204295b0a2f7c591d5ca434475d6d7890e89febaaf39a307`.
The input manifest identifies the exact versions. Concurrent live edits, if
any, are recorded in the delivery manifest and are not silently substituted.

The curve facts used here are the different form of Riemann–Hurwitz and its
local inequality, in the Stacks Project, [Lemma 53.12.2, tag 0C1D](https://stacks.math.columbia.edu/tag/0C1D)
and [Lemma 53.12.4, tag 0C1F](https://stacks.math.columbia.edu/tag/0C1F).
The complete [Section 53.12](https://stacks.math.columbia.edu/tag/0C1B) is frozen.
For a separable map, these give
`2g_X-2 = deg(f)*(2g_Y-2) + sum_x different_x`, with
`different_x >= e_x-1`, and equality locally in the tame case.

Frobenius factorization and invariance of genus under purely inseparable maps
between smooth proper curves are covered by [Proposition 53.13.7, tag 0CD2](https://stacks.math.columbia.edu/tag/0CD2)
and [Lemma 53.13.5, tag 0CD0](https://stacks.math.columbia.edu/tag/0CD0).
Their complete [Section 53.13](https://stacks.math.columbia.edu/tag/0CCV) is frozen.
Below, the specialization to `k(X)` and the Kummer-cover genus are also
derived explicitly, so the genus value is not imported without hypotheses.
The passage from a function-field embedding to a nonconstant map of normal
projective curves uses [Theorem 53.2.6, tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1),
whose complete theorem page and proof are also frozen.

For the character bound I independently checked [Kowalski, *Exponential sums
over finite fields: elementary methods*, Theorem 3.1](https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf#page=33),
version September 14, 2021, printed page 31 / PDF page 33. Its hypothesis is
a character of order `d>1`, `d | q-1`, and a polynomial which is not a
`d`-th power over the algebraic closure. With `m` distinct geometric zeros,
the complete sum is bounded by `(m-1)*sqrt(q)`. Neither squarefreeness,
prime character order, nor degree below `q` is required. The downloaded full
PDF has SHA-256
`ff30b82d143cedcaf76f1ef2f15a49856c0eabc2c95ba7ac0da2e3e43da9a866`,
matching the earlier review. Full text and the theorem page's text are retained.

## 1. Four fibers, wild ramification, and inseparability

Let `k` be algebraically closed of odd characteristic `p`, and let
`P in k(X)` be nonconstant. Assume `y,w in k*` and `y != w`.
On the target projective line,

    div(F_(y,w)) = [y] + [w] - [0] - [infinity].

Thus, for `a` one of these four target points and `x` in its `P`-fiber,

    ord_x(F(P)) = ord_a(F) * e_x(P) = +/- e_x(P).

The four fibers are disjoint. This is a statement about divisor support of
the outer function, not about all critical values of either map.

First suppose `P` is separable, of degree `D`. If `F(P)` were an `ell`-th
power, `ell != p` prime, every `e_x` in these four fibers would be divisible
by `ell`. Since each fiber has total multiplicity `D`, it would have at most
`D/ell` geometric points. For each fiber its contribution to
`sum(e_x-1)` is therefore at least `D-D/ell`. Riemann–Hurwitz gives

    4D*(1-1/ell) <= sum_x(e_x-1)
                 <= sum_x different_x = 2D-2.

But `4D*(1-1/ell) >= 2D` for every `ell >= 2`. The contradiction proves
(1) for separable `P`. One must not replace the second inequality by an
equality in a wild case. Wild ramification increases the different relative
to `e_x-1` and only reduces the available ramification budget.

For general `P`, choose the maximal `a >= 0` with `P=S^(p^a)` in `k(X)`.
It exists and is finite: in this perfect constant field, a rational function
has zero derivative exactly when it belongs to `k(X^p)=k(X)^p`, and taking
a `p`-th root divides its positive map degree by `p`. Maximality makes
`S` separable. Put `q=p^a`, `y0=y^(1/q)`, `w0=w^(1/q)`. These roots are
unique in `k`, nonzero, and distinct. Frobenius gives the exact identity

    F_(y,w)(S^q)
      = (S^q-y0^q)*(S^q-w0^q)/S^q
      = (F_(y0,w0)(S))^q.

Using the unchanged anchors over a general algebraically closed field would
be wrong; their Frobenius roots are essential. For anchors in `F_p` the
roots do equal the anchors. Multiplying every valuation by `q` preserves
divisibility by `ell != p`, so the separable contradiction proves (1) in
full generality.

There is a useful strengthening. Write `G=F_(y0,w0)(S)`. Its derivative is

    G' = S' * (1-y0*w0/S^2),

which is nonzero because `S' != 0` and `S` is nonconstant. Hence `G` is not
a `p`-th power either. Combining this with (1), the positive gcd of all
nonzero divisor multiplicities of `G` is exactly `1`, and that of `F(P)`
is exactly `p^a`.

The exclusion `ell != p` is real. For any odd `p`, take `P=X^p` and
distinct `y,w in F_p*`. Then `F_(y,w)(X^p)=F_(y,w)(X)^p`.
The reset removes prime-to-`p` power indices; it does not remove inseparable
`p`-power structure. Odd characteristic is the task's standing assumption;
the prime-to-characteristic four-fiber proof itself does not use `p>2`.

## 2. The equivalent superelliptic argument

Interpret `T^ell=F(Z)` as its smooth projective normalization over `k`, not
as an assertion that an arbitrary affine or plane closure is smooth.
At `Z=y`, the valuation of `F` is one, so `T^ell-F` is Eisenstein in the
local discrete valuation ring. The function field extension has degree
`ell`, is connected, and is separable since `ell != p`.

At each of `y,w,0,infinity`, the valuation is `+1` or `-1`, coprime to
`ell`, giving total ramification of index `ell`. Away from these points,
the equation is a unit Kummer equation with invertible derivative in `T`,
so it is unramified. All four ramification points are tame. Applying
Riemann–Hurwitz to this cover yields

    2g-2 = -2ell + 4*(ell-1) = 2ell-4,
    g = ell-1 >= 1.

If `F(P)=Q^ell` with nonconstant `P`, the functions `(P,Q)` induce a
nonconstant map from `P^1` to this normalized curve. A separable such map
contradicts Riemann–Hurwitz, since its right-hand side is nonnegative and
its left-hand side is `-2`. An inseparable map first factors through a
Frobenius twist of `P^1`, again of genus zero, with a separable remaining
map, and gives the same contradiction. This validates the equivalent
argument even in the inseparable case.

The genus formula here is unavailable for `ell=p`: that root extension is
inseparable. Also revise “four fibers, not two or three, are decisive” to
“four fibers obstruct every prime-to-characteristic root order; three
already obstruct prime root orders at least three.”

## 3. Equation (2), composite exponents, and geometric characters

For `f in k(X)*`, factor its numerator and denominator over `k`:

    f = c * product_(alpha finite) (X-alpha)^m_alpha.

All valuations divisible by an integer `d>=1` imply
`f=(c^(1/d)*product (X-alpha)^(m_alpha/d))^d`; the converse is immediate.
The infinity valuation is the negative sum of the finite valuations.
This elementary criterion is for the rational function field `k(X)`;
one should not transplant it without qualification to arbitrary curves.

Let `m` be the divisor-multiplicity gcd of `R=F(P)`. Section 1 gives
`m=p^a`. The gcd for `H=R^e` is `e*p^a`. Consequently, for every
`d | p-1`, including composite `d`,

    H is a geometric d-th power
      iff d | e*p^a
      iff d | e.

This proves (2). It uses full divisibility, including prime-power valuations
of `d`, not just the set of primes dividing `e`. For example, an outer
exponent `6` does not create a geometric fourth power, whereas `12` does.

For a multiplicative character `eta` of exact order `d`, geometric
triviality of its Kummer pullback is precisely this `d`-th-power criterion.
Thus the exceptional characters are exactly `eta^e=1`; their count is
`gcd(e,p-1)` in the cyclic character group of order `p-1`.
In this family they have actual coefficient `s`, because the given map is
literally `R^e`, without an additional scalar twist.

Apply the argument at every accepted fold, with any earlier powered history
as `P`. The outermost **accepted** exponent controls the prime-to-`p`
index. Paid no-ops do not supply a new exponent or change the map.
Repeated squaring in odd characteristic therefore never makes the current
map a geometric fourth, eighth, or `2^k`-th power solely by accumulating
the earlier squarings.

In contrast, if exponents contain `p`, the inseparable exponent can
accumulate: starting with separable `P`, its `p`-adic inseparable exponent
after accepted stages is `sum_j v_p(e_j)`. This has no additional
multiplicative-character exception over `F_p`, whose character orders all
divide `p-1`; powering by `p` also fixes every value in `F_p`.

Geometric non-power is not a finite-field image classification. An explicit
algebraic illustration over `F_5` is

    P=X^5-X+3,
    R=(P-1)*(P-2)/P.

Here `P'=-1`, and (1) shows that `R` is not a geometric square. Nevertheless
every affine `x in F_5` has `P(x)=3` and `R(x)=4`, a square. Thus its
quadratic residual character coefficient equals `1`. This is proved using
`x^5=x`, without sampling or a sweep. The anchors `1,2` are unavailable
from this `P`'s affine output law; the example is not claimed to be a
reachable accepted history or a factoring candidate. It isolates exactly
why a geometric theorem cannot alone prohibit finite-field coincidences.

## 4. Equation (3): all character orders, poles, and infinity

Now assume `P,y,w` are defined over `F_p`. Let `D` be the actual degree
of the reduced rational map, including its inseparable degree. The outer
homogeneous map

    [u:v] -> [(u-yv)*(u-wv):u*v]

has degree two and no basepoint: at `u=0` the first coordinate is
`yw*v^2 != 0`, and at `v=0` it is `u^2 != 0`. Composing with a degree-`D`
map gives degree exactly `2D`. Thus a reduced affine expression `R=A/B`
has `max(deg A,deg B)=2D`, and `deg A+deg B<=4D`.

Define the unnormalized residual law and its transform by

    nu_R(b) = #{x in F_p : R(x)=b}/p,  b in F_p*,
    M_R(psi) = sum_(b in F_p*) nu_R(b)*psi(b).

For a nontrivial character `psi` of exact order `d>1`, extend `psi(0)=0`
and set `Q=A*B^(d-1)`. At any affine nonzero finite output,
`psi(Q(x))=psi(A(x)/B(x))`. At a zero of either `A` or `B`, the polynomial
`Q` vanishes and contributes zero. Reducedness prevents common zeros;
`d-1>0` makes the pole exclusion exact. Therefore

    p*M_R(psi) = sum_(x in F_p) psi(Q(x)).

Further, in `k(X)`, `Q=R*B^d`. If `Q` were a geometric `d`-th power,
so would `R`. For composite `d>1`, choosing any prime `ell|d` would then
make `R` an `ell`-th power, contradicting (1), since `d|p-1`.
This verifies the higher-order hypothesis directly. No simple pole is used.

The distinct finite geometric roots of `Q` are exactly those of `A*B`;
their count `m` is at most `4D` and is positive. Theorem 3.1 gives

    |M_R(psi)| <= (m-1)/sqrt(p) <= (4D-1)/sqrt(p) = delta.

This is (3). High multiplicities, an inseparable `P`, high `d`, and degree
greater than `p` cause no missing condition. The large encoding exponent
`d-1` does not increase the distinct root count.

There is **no additional infinity or pole correction** in this affine
argument. The sum is over `F_p`, so the input `infinity` is never added.
Finite inputs mapping to infinity are already zeroed by `B^(d-1)`.
The infinity valuation is still included in the geometric non-power proof;
if all finite valuations were divisible by `d`, their negative sum at
infinity would be too. A projective-input normalization would be a different
formula. For the trivial character use `M_R(1)=s` separately: taking `d=1`
in this polynomial encoding would omit the poles incorrectly.

The trivial bound `|M_R(psi)|<=s` is also available. In particular, (3) can
be entirely uninformative when `D` is large; it does not preclude the
finite-field example above.

## 5. Equation (4) and the evaluator cost

For `H=R^e`, positive `e` preserves zero, infinity, and their union, so the
residual mass remains `s`. On nonzero finite outputs,

    M_H(eta)=M_R(eta^e).

Let `n=p-1`, `g=gcd(e,n)`, and `K={eta:eta^e=1}`. Then `|K|=g`
and `M_H(eta)=s` on `K`, including the trivial character. For each other
character, `psi=eta^e` is nontrivial and (3) applies with the degree of `R`
before this last power.

For `C_H(c)=sum_(ab=c) nu_H(a)*nu_H(b)`, character orthogonality gives

    E_mul(H) := sum_c C_H(c)^2 = (1/n)*sum_eta |M_H(eta)|^4,
    v_H = (1/n)*sum_eta |M_H(eta)|^2.

Separating `K` therefore gives exactly

    E_mul(H) = g*s^4/n + Rem,
    Rem = (1/n)*sum_(eta notin K) |M_R(eta^e)|^4 >= 0,
    Rem <= delta^2*(1/n)*sum_(eta notin K) |M_H(eta)|^2
        = delta^2*(v_H-g*s^2/n).

This is (4), with nonnegative bracket. It remains valid for `s=0`, `e=1`,
or `g=n`; in the last case the remainder and bracket both vanish.
The exceptional term is an exact contribution, not necessarily the main
term in size. This energy includes diagonal pairs; it is not by itself the
accepted `sum Gamma^2` term or a positive drift/success lower bound.

Binary powering the two already evaluated projective coordinates costs
`O(log e)` modular multiplications for `e>=2`; for `e=1` the additional
powering work is zero. The complete fold also has its constant arithmetic
cost. Coprime coordinates remain coprime after taking positive powers,
and the rational-map degree becomes exactly `2eD`, including inseparable
degree. Degree growth does **not** force an implementation to expand the
polynomials or pay that degree as point-evaluation work. It does enter the
next stage's spectral error: one may not charge a degree-dependent theorem
as though its error grew only logarithmically with `e`.

Exponent selection, representation, arithmetic bit costs, acquisition of
fresh anchors by evaluating the current circuit, gcds/inversions, and paid
failed charts remain in the computational ledger. Equations (1)–(4) supply
neither an `N`-only method guaranteeing useful `g` nor favorable CRT
separation. They do not convert this per-point cost into a complete
factoring runtime claim.

## 6. Equation (5) and the support boundary repair

Let `J` be a nonconstant rational outer map. Count `r` distinct target
values `a` with `m_a=ord_a(J) != 0` and `gcd(m_a,ell)=1`, where `ell != p`
is prime. Other zero/pole support values may exist and are not counted.
If `J(P)` is an `ell`-th power, then

    ell | m_a*e_x(P)  implies  ell | e_x(P)

above each of the counted target values. For separable `P` of degree `D`,
the same fiber budget proves exactly

    r*D*(1-1/ell) <= 2D-2.                         (5)

For inseparable `P=S^(p^a)` put `D0=deg S`, so `D=p^a*D0`.
Each target value has a unique Frobenius root, and its local indices are
`p^a` times those of the corresponding `S`-fiber. Since `ell != p`, the
condition transfers to `S`. The sharper valid statement is

    r*D0*(1-1/ell) <= 2D0-2,
    r*D*(1-1/ell) <= 2D-2*p^a <= 2D-2.

Thus (5) remains necessary with total degree `D`; one must not apply the
separable Riemann–Hurwitz formula directly to inseparable `P`. Its converse
is not asserted. If `ell=p`, this reasoning fails: composing any `F_p`
rational function `J` with `X^p` gives `J(X)^p`, regardless of its number
of prime-to-`p` support multiplicities. The four-support `F` itself already
provides a counterexample to such an extension of (5).

The boundary computations are strict:

- `r=4, ell=2` would require `2D<=2D-2`, impossible.
- `r=3, ell=3` gives the same impossible inequality.
- `r=3, ell>3` has an even larger left-hand side relative to `2D`.

For squares there is an additional parity restriction independent of
Riemann–Hurwitz: `sum_a ord_a(J)=0`, so the number of odd multiplicities
is even. Thus “at most three” follows as a loose bound from (5), but the
actual allowed number of counted odd values is `r=0` or `r=2`.
There is no genus-zero square-root cover with exactly three odd branch
values. This is the substantive boundary wording repair.

Three **total** zero/pole support values are different. For the stated
coalescence with `y=w != 0`,

    div((Z-y)^2/Z) = 2[y]-[0]-[infinity].

The support size is three, but for `ell=2` only `0,infinity` are counted,
so `r=2`. The square-root cover has precisely those two tame branch
points and genus zero by the same Riemann–Hurwitz computation. For
`ell>=3`, `ell != p`, all three displayed multiplicities are coprime to
`ell`, and the three-fiber obstruction applies. These are divisor/genus
observations only. The next sampler's moment law, planted fibers, reachable
states, acquisition work, and factoring performance are not reviewed here.
The accepted law requiring `y != w` cannot be reused after coalescence.

A rational function with exactly two total divisor support values is
`c*M(Z)^m` for a Möbius coordinate `M` and a nonzero integer `m`, because
its two valuations must be opposite. This explains the cyclic-group
observation. Neither two total support values nor a genus-zero cover alone
constitutes a factoring algorithm.

## Delivery and remaining obligation

The geometric accumulation proposal is resolved negatively within its exact
scope: earlier prime-to-`p` powers do not compound through the distinct,
nonzero two-anchor fold. The necessary revisions are the square-support
parity qualification, the three-fiber threshold for `ell>=3`, and explicit
characteristic/separable-degree conditions on (5).

To change this conclusion for a new computation, one must change the divisor
pattern or prove useful nonexceptional finite-field correlations with paid
input acquisition and complete work accounting. No such computation or bound
is accepted here. The coalesced-anchor direction belongs to the parent's
separate development, and the scalar-product direction remains outside this
root-density audit.

The companion exact certificate script checks algebraic identities used in
the proofs, including Frobenius anchor transport, the strict boundary gaps,
and the displayed finite-field coincidence by polynomial congruence. These
checks are not a proof of Riemann–Hurwitz, a candidate run, a prime/depth
sweep, or a Lean formalization. The delivery manifest inventories all files
and hashes; the checksum file additionally covers the manifest. No shared
source, Lean, state, package, commit, publication, or delegation was changed
or performed.
