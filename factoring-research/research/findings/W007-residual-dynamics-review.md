# W007 residual dynamics — independent audit

2026-10-08. Finite-field adaptive absorption only. The fixed rational cover,
the Prouhet–Tarry–Escott families, and the tau conversion are outside this
review and are left as already separated. No factoring candidate was run, no
shared file was edited, and no package was installed.

**Disposition.** The residual identity is an exact one-step law for every
probability distribution on an odd prime field, not a growth theorem and not
a factoring bound. A large zero atom does inflate total collision mass while
the next absorption rate depends only on the nonzero residual. That split is
visible on a reachable depth-1 state at p=5, where expected collision mass
rises and expected residual mass falls. Persistent doubling is already false
on the generic branch: the second-step multiplier tends to 3/2, and for
p=3,5,7 the second-step drift is negative. Through three generic steps the
expected local root count is the exact rational function below, which tends
to 7 rather than to the degree cap 8. No identity was found that acquires the
training coefficients in o(k^2) multiplications or replenishes a reservoir
point in o(k). One fresh evaluation, once the coefficients are known and
2^k < p, needs at least k non-scalar multiplications. The explicit triangular
chain costs k(k-1)/2 multiplications; that count is not promoted to a general
circuit lower bound. Verified factoring improvement: NONE.

The checker
[verify.py](W007-residual-dynamics-review-scratch/verify.py)
compares the drift with the value pushforward for every square shift on every
odd prime below 60, and compares the closed forms below with direct
enumeration. The read scope for composition algorithms is
[literature-scope.md](W007-residual-dynamics-review-scratch/literature-scope.md).

## 1. The law that survives

Fix an odd prime p and an arbitrary map f from the field to itself. Let
μ(y) be the fraction of inputs with f(x)=y, and draw a from μ. The next value
is y(y-a). Write z=μ(0), ν(0)=0, and ν(y)=μ(y) for y≠0. The parent's
residual quantities are

    v = Σ ν(y)^2,                 t = Σ ν(y)^3,
    R = Σ ν(y)ν(-y),
    Q = Σ_{y,w} ν(y)ν(w)ν(y+w),
    D = Σ_y ν(2y)ν(y)^2.

Let primes denote the pushforward. Then, conditional on μ,

    Δz = ν(a),
    E[Δz] = v,
    E[Δv] = z R + Q - D - t.

The zero-fraction identity is the one already accepted for every
characteristic: the fibers at 0 and at a are disjoint precisely when a≠0, so
z' = z+μ(a) when a≠0 and z'=z when a=0. Averaging ν(a) against μ deletes the
zero atom and leaves v. In particular E[Δz]=c-z^2, since v=c-z^2 and
c=Σ μ(y)^2. Total collision mass is the wrong energy because the next
absorption rate is v, not c.

The collision update in odd characteristic is the accepted formula

    c'(a) = c + Σ_y μ(y)μ(a-y) - μ(a/2)^2.

It is inclusion–exclusion on the events Y=W and Y+W=a. Those events meet only
at Y=W=a/2, so the subtraction is one point, not a global diagonal, and the
sum is over ordered pairs, so no factor 1/2 belongs there. Averaging a against
μ gives

    E[Σ_y μ(y)μ(a-y)] = Σ_{y,u} μ(y)μ(u)μ(y+u).

Split the triples by whether a coordinate is zero. The (0,0) triple contributes
z^3. The two mixed triples with exactly one of y,u equal to zero contribute
2zv. The triples with y=-u≠0 contribute zR. The triples with y,u,y+u all
nonzero contribute Q. The half-argument average is

    E[μ(a/2)^2] = Σ_b μ(2b)μ(b)^2 = D + z^3,

because ν drops only the b=0 term μ(0)μ(0)^2=z^3, and in odd characteristic
2b=0 forces b=0. The two copies of z^3 cancel, and

    E[Δc] = 2zv + zR + Q - D.

The zero-atom square changes by

    E[(z+Δz)^2 - z^2] = 2z E[Δz] + E[(Δz)^2] = 2zv + t,

since E[(Δz)^2]=Σ_{a≠0} μ(a)^3=t. Subtracting from E[Δc] leaves
E[Δv]=zR+Q-D-t.

Two algebraic remarks that are easy to drop:

- In odd characteristic the diagonal part of Q is exactly D. Indeed y=w≠0
  forces 2y≠0, so every such ordered pair is admitted by ν, and Q-D is the
  off-diagonal nonzero triple sum. The parent's phrase "off the equal-input
  diagonal" is correct under that hypothesis. It is not an identity D=t.
  Equality D=t holds for the uniform law and fails for the depth-1 law: there
  t has numerator 4p-11 while D still depends on χ(2).
- Characteristic 2 deletes the cross term 2zv and makes a/2 undefined. The
  displayed E[Δv] is then the wrong polynomial. The zero-fraction identity
  E[Δz]=v survives. This review does not extend the residual formula to F_2.

The same expansion holds for every probability law, polynomial image or not.
What the recurrence adds is reachability. A sum-free nonzero support with
R=Q=D=0 has E[Δv]=-t, as the parent says; that is a law, not yet a reachable
polynomial. Section 3 supplies reachable laws with the same sign.

Drawing a independently of μ, or drawing a constant, is a different algorithm.
The uniform-parameter alternative has E[Δz]=(1-z)/p, not v.

## 2. What the zero atom does, and what it does not do

Write c=z^2+v. The one-step changes split as

    E[Δ(z^2)] = 2zv + t,          E[Δc] = 2zv + zR + Q - D.

The shared 2zv is the cross term in the enlarged zero atom. It increases c and
does not increase v. The summand t is the expected square of the absorbed
nonzero fiber: that square leaves the residual and becomes part of (z')^2.
The term zR is exactly the contribution of the draw a=0. On that draw Δz=0
and Δv=R deterministically, because c'(0)-c=R. Sampling the current zero value
merges opposite fibers and does not plant a new root.

Thus a growing zero atom can make c, and any score built from c, increase while
the future absorption rate v decreases. It does not by itself make E[Δz] look
large: E[Δz] already excludes z^2. The illusion is using c, or a frozen zero
atom, as evidence that later fresh probes are becoming more productive.

Concrete reachable witness, p=5, P(X)=X(X-1). The value counts are

    n(0)=2, n(1)=1, n(2)=2, n(3)=n(4)=0.

So z=2/5, v=1/5, c=9/25. The next training value is drawn with these weights.
The three positive-weight images and their collision counts Σ n^2 are

    a=0 (weight 2): counts (2,1,0,0,2), collision 9, nonzero square-sum 5;
    a=1 (weight 1): counts (3,0,2,0,0), collision 13, nonzero square-sum 4;
    a=2 (weight 2): counts (4,0,0,0,1), collision 17, nonzero square-sum 1.

Hence E[c']=13/25 and E[v']=16/125. Collision mass rises by 4/25. Residual
mass falls by 9/125. Here t=9/125 as well, and zR+Q-D=0, so the whole residual
drift is -t: the additive contribution cancels and the absorbed fiber is paid
entirely out of v. Future E[Δz] falls from 1/5 to 16/125.

The other direction also occurs and is not an illusion. The pure power
x |-> x^{2^k}, reached by k successive zero training values, keeps a single
root at 0 and puts the remaining mass on fibers of size gcd(2^k,p-1). Residual
mass is then large while z stays 1/p, so the next nonzero draw really does
absorb a heavy fiber. Section 5 records why global stopping rarely allows that
branch to continue.

## 3. Exact controls through depth three

**Depth 0.** For μ uniform, direct counting gives the parent's values

    z=1/p,  v=R=(p-1)/p^2,  Q=(p-1)(p-2)/p^3,
    D=t=(p-1)/p^3,  E[Δv]=(p-1)(p-3)/p^3.

The p=3 value is zero. For every odd prime the first map is deterministic in
the collision count: Σ n(y)^2 = 2p-1 whatever a is. If a≠0, the law is a
translate of the squares by a nonzero square, root count is exactly 2, and

    v=(2p-5)/p^2.

If a=0, the law is the squares, root count stays 1, and v=2(p-1)/p^2.
Unconditionally

    E[v]=(p-1)(2p-3)/p^3,

so the residual scale p v tends to 2. The ratio against the initial
(p-1)/p^2 is (2p-3)/p = 2-3/p. That is one step, not a doubling law.

**Depth 1, generic branch.** Condition on a0≠0. Every such law is a square
translate n(y)=1+χ(y-b) with χ(-b)=1 and b≠0, and χ the Legendre symbol. For
every such translate the next residual drift is independent of b:

    p^3 E[Δv] = p^2 - 13p + 32 + χ(-1) + 2χ(2).

The numerator equals -1 at p=3, and -9 at p=5 and p=7. Over the four
character combinations its minimum is p^2-13p+29, which equals 7 at p=11 and
is positive for every larger prime. In particular the reachable state
P(X)=X(X-1) on F_5, and the same branch on F_3 and F_7, have negative expected
residual drift. This kills the rule "every reachable state on an odd prime
p>3 has E[Δv]≥0".

The resulting expectations on this branch are deterministic enough to sum.
Root counts m mean p z. With ε=χ(-1)+2χ(2),

    m_1 = 2,
    v_1 = (2p-5)/p^2,
    E[m_2] = (4p-5)/p,
    E[v_2] = (3p^2 - 18p + 32 + ε)/p^3,
    E[m_3] = (7p^2 - 23p + 32 + ε)/p^2.

So after one generic step p v = 2-5/p, and after two steps p E[v] tends to 3.
The second-step ratio tends to 3/2, not to 2-3/p. After three steps the
expected root count tends to 7, while the degree cap is 8. Both the 3/2 limit
and the depth-3 count are theorems for every odd prime, not fits. The checker
reproduced E[m_3] for every odd prime below 40.

Derivation of the depth-1 drift, enough to audit the numerator. For
n(y)=1+χ(y-b) and b≠0,

    Σ_y n(y)^2 = 2p-1,
    Σ_{y,w} n(y)n(w)n(y+w) = p^2 + p χ(-b),
    Σ_y n(y)n(-y) = p - χ(-1).

The cubic character sum is p χ(-b): substitute w=yu and use
Σ_{y≠0} χ(y)=0 except on the line u=-1, which produces the factor p. The
opposite sum is -χ(-1) after the substitution y=bz reduces it to
Σ χ((z-1)(z+1))=-1. The complete half-sum is

    Σ_y n(2y)n(y)^2 = 2p - 1 - 2χ(2) - χ(b),

because the only surviving cross term is Σ χ((y-b)(2y-b))=-χ(2). Restrict to
χ(-b)=1, so n(0)=2 and χ(b)=χ(-1). Removing the zero coordinate from Q, R, D,
and t, then forming n(0)R_count + Q_count - D_count - t_count, produces the
numerator above. The square law b=0 is the same calculation with a separate
half-sum: D_count is 4(p-1) when χ(2)=1 and 0 otherwise, and

    p^3 E[Δv] = (p-1)(p-11)  if χ(2)=1,
                (p-1)(p-7)   if χ(2)=-1.

That branch also has negative drift at p=3,5,7. It is the local law of a0=0.

These identities refute two plausible growth rules on reachable states.

- "Repeat the first-step factor 2-3/p while the map is nonconstant." On the
  generic branch the next factor tends to 3/2, and at p=5 it is 16/25<1.
- "E[Δv]≥0 for every reachable law once p>3." False for every a0≠0 law at
  p=5 and p=7, and for the square law at those primes.

They do not refute growth. For every p≥11 the generic second step has positive
drift, and the expected root counts 2, then 4-5/p, then 7-O(1/p), are still
increasing.

**Not proved past depth three.** The triangular extrapolation would send the
expected root count to 1+k(k+1)/2, hence to 11 after four steps. That
statement is not a theorem. Exact enumeration on the generic branch, recorded
only as finite values, gives expected root counts

    p=17: 38731/4913 ≈ 7.883,
    p=31: 271369/29791 ≈ 9.109,

both below 11, with degree cap 16. The same search finds a branch that does
hit the cap. On F_17 the coefficients (a0,a1,a2,a3)=(1,8,2,15), each obtained
as the value of the preceding polynomial at a field element, satisfy P_4(x)=0
for every x except x=9. Sixteen roots, one short of the whole field. The depth-3
prefix (1,8,2) already has eight roots, the degree cap, and nonzero square-sum
V=65, so p v=65/17<4. Hitting the degree cap on one branch does not lift the
expectation. A pointwise rule "every reachable root count stays at most
1+k(k+1)/2" is false at this example, since 16>11. The expectation rule is
still open at depth 4.

The repeated-zero tower is a pointwise counterexample to "p v ≤ k+1". On F_17,
three zero trainings produce x |-> x^8. The nonzero fibers are two sets of
size 8, so V=128 and p v=128/17>4. Section 5 explains why this tower is not
the continued global process.

No depth curve is being promoted. The all-prime statements stop at E[m_3].

## 4. If the triangular increments continued, they would lose to rho

This conditional comparison is not a theorem about the algorithm. It only
prices the unproved extrapolation against controls already in the project.

The accepted cost shape, from the tau-acquisition disposition's corrected
ledger, is k^2 training multiplications plus k/s_k fresh-probe multiplications
when the proper-factor probability is s_k. The W006 batch review's corrected
detector, used here only as a paid known-scale control, has expected bit work
O(√p · poly(log N)) on distinct odd semiprimes. Pollard rho is the same scale.

On the generic branch the proved values are s_3 = Θ(1/p) after a constant
number of stages, because the expected root count tends to 7. Stopping at
depth 3 and probing is Θ(p) modular multiplications, worse than √p. If the
unproved bound E[m_k] ≤ 1+k(k+1)/2 held for all k with 2^k < p, then
s_k = O(k^2/p) and the ledger would minimize at k=Θ(p^{1/3}), at cost
Θ(p^{2/3}), still worse than √p by a power. A strict improvement over that
control needs expected root counts growing faster than every multiple of k^2,
or a subquadratic acquisition method. Neither is established. The parent's
pseudorandom guess Q≈(1-z)^3/p, which produces linear residual growth and
quadratic root growth, is consistent with the proved range and is still not a
law. The depth-2 collision count can increase by more than p on a single
reachable state (the power tower), so "add at most p to Σ n(y)^2" is not an
invariant either.

The degree cap m ≤ 2^k for a nonconstant function is real and is attained by
(1,8,2,15) mod 17. It does not rescue the cost. Reaching expected root count
√p under the cap still forces k ≥ (1/2)log2 p and, with one probe per success
at that height, a √p · log p probe bill. The proved expectation at depth 3 is
already a constant, not 8 in a way that starts an exponential. Depth 4 is where
a cap-tracking law and a triangular law first separate by a fixed ratio
(16 against 11), which is why that expectation is the next exact question
rather than a larger search.

## 5. Factors, masks, CRT, and stopping

Scope of the fresh-probe law. Let N=pq with distinct odd primes, and let P be
any already constructed polynomial with integer coefficients, or any residue
polynomial computed in Z/NZ. Let z_p and z_q be the fractions of roots as
functions on the prime fields. For x uniform in Z/NZ and independent of P,

    Pr[gcd(P(x),N)=N] = z_p z_q,
    Pr[1 < gcd(P(x),N) < N] = z_p + z_q - 2 z_p z_q.

The CRT components of a fresh x are independent. This is conditional on the
realized polynomial. Averaging over histories gives E[z_p+z_q-2 z_p z_q]. It
does not give E[z_p]E[z_q], because the training residues are shared and
(z_p,z_q) are dependent. It does not survive an arbitrary stopping rule that
filters histories and then treats a later probe as independent of the filter.
It does survive a probe drawn after the history is fixed.

Each training residue is such a probe of the polynomial before the update.
Its proper gcd is a success and stops the run. A full gcd N on that residue
is an exhausted draw, not a factor. Counting the training gcd and a second
probe at the same point is double counting. Prime powers and products of more
than two primes are outside the two-factor display; a proper prime-power gcd
needs its own valuation test. The factor 2 can be removed by a constant-time
trial before this analysis. None of this is a stopped-process independence
theorem.

Pre-multiplication tests change the masked null set, not the main term while
both zero fractions are small. Evaluating the tower produces the intermediates
y, y(y-a0), .... Roots persist forward: a prime that divides an intermediate
divides every later value. The converse is false. A new fiber can make the
product divisible by q while the previous value is divisible by p only.

Explicit mask, N=15, current polynomial the identity, probe x=3, constant
a=13:

    gcd(3,15)=3,    gcd(3-13,15)=gcd(10,15)=5,    gcd(3·(-10),15)=15.

The product is a full gcd. Each factor before the multiplication is a proper
factor. Discarding the intermediates loses both. An endpoint full gcd is
different: gcd(0,15)=15, and no intermediate supplies a proper divisor. Full
gcd N is not success. When z_p and z_q are both small, the salvageable mask
has mass O(z_p z_q), while the proper-factor mass of the final value is
z_p+z_q-2z_p z_q. The tests are mandatory and lower order in that range.
They are not a second success channel to be added as an independent Θ(z_p+z_q).

Global stopping deletes most local zero trainings. The algorithm tests
gcd(a_j,N) before accepting the update. A proper divisor stops the run with a
factor. The polynomial continues only when that gcd is 1 or N. Locally, a≡0
mod p and a≢0 mod q is success, not a continued square map. The continued
zero update a≡0 mod p occurs only when a≡0 mod N. For the first step that has
probability 1/(pq), not 1/p. The power tower of section 3, which really does
inflate v, continues globally only along that joint-zero sequence. Its
probability is about N^{-k}. It must not be averaged into the generic branch
as if a local zero were free. The generic closed forms condition only on
a0≠0, and then they average later training values without removing later
proper gcds. They are local expectations, not survival-conditional
expectations. Paths that hit a proper gcd at step 1 or 2 have already
succeeded and must be counted as successes, not as further root growth.
Replacing the survival law by the unstopped expectation would mis-price those
early hits. This review does not compute the survival-conditional generating
function.

One-sided saturation remains a real success if it is ever reached. If the
function is identically zero mod p and not mod q, every fresh value is
divisible by p, and the probe gcd is p whenever it is not also divisible by q.
Reaching that state means at least p roots, hence depth at least log2 p for a
nonconstant stage, and the training bill through that depth is still only
(log p)^2 multiplications if one pays the explicit chain. The obstruction is
not the evaluation cost of the last probe. It is whether the expected root
count ever gets that large. Depth three says the expectation is still a
constant.

## 6. Reservoirs and the missing operation

Storing L inputs and their current values updates in O(L) arithmetic steps per
stage: each stored y becomes y(y-a). Using a stored input as the training
residue sets that value to 0 modulo N. The slot remains a global root. A later
draw from it returns a=0 and gcd(0,N)=N. Each reservoir slot therefore
supplies at most one nonzero training value, and using it plants a root at
both primes at once. Replenishment is a fresh evaluation of the current tower.

Once a0,...,a_{k-1} are known field elements, the tower at one new point is
the chain y |-> y(y-a_i). That is k multiplications and k subtractions.
It is optimal for a generic point while 2^k < p. The composed polynomial is
monic of degree 2^k. Additions and multiplications by the coefficient field do
not increase degree. A non-scalar product of two polynomials at most adds
their degrees, so m non-scalar multiplications produce degree at most 2^m.
Reaching degree 2^k forces m≥k. The bound applies to any circuit correct for
the polynomial, hence at a generic probe. It does not apply to a circuit that
is only required to be correct at one known root. It also does not apply
after 2^k ≥ p, where X^p-X can collapse the function degree; by then the
degree cap is already the whole field and the evaluation lower bound is the
wrong question.

Splitting the tower into two halves of length k/2 and evaluating the outer
half on the inner values returns the recurrence T(k)=2T(k/2), which is still
Θ(k) per point. Deduplicating equal intermediate values saves work only when
distinct probes collide. Random probes collide when their number is on the
scale of the reciprocal square root of the collision probability, which at
early depth is the √p scale already priced by rho. That is not an asymptotic
saving for k successive training points.

Dense modular composition does not change this arithmetic. The checked
abstract of Neiger–Salvy–Schost–Villard, arXiv:2110.08354v2, prices
composition of dense degree-n polynomials modulo a third polynomial. Here the
dense degree would be n=2^k, so that family of algorithms is exponential in
the depth. Brent and Kung (1978) appear there only as the previous dense
bound; that paper was not opened, and neither result is used as a lemma.

The explicit acquisition cost, with prefixes stored, is exactly

    Σ_{j=1}^{k-1} j = k(k-1)/2

multiplications of the form y(y-a), plus the training residues, the gcd tests,
and one subtraction per multiplication. Task A's ledger of the same shape is
confirmed. This is not a proof that every circuit needs that many
multiplications. The degree bound applied to the last training value alone
gives only Ω(k), because one multiplication might carry positive degree in
two training indeterminates and later cancel. No such cancellation was found.

**Missing operation.** A straight-line program, on inputs r_0,...,r_{k-1} in
Z/NZ, that outputs every a_j=P_j(r_j) for the nonautonomous tower
P_0=X, P_{j+1}=P_j(P_j-a_j), using o(k^2) ring multiplications. Equivalently,
given generic coefficients already computed, a program that returns the L
values of the tower at L fresh points using o(kL) non-scalar multiplications
for large L. The one-point case of the second problem is impossible when
2^k < p. The triangular problem and the large-L problem are open because
cross-cancellation has not been ruled out, and no replacement identity was
derived. An oracle that samples from μ, or that returns heavy fibers without
exhibiting the inputs, is not this operation.

## 7. Next decisive question

Prove or refute, for every odd prime and the generic branch a0≠0, that the
expected root count after four adaptive steps equals some specific rational
function of p, χ(-1), and χ(2), and decide whether its limit is 11. The
depth-3 predecessor is

    E[m_3] = (7p^2 - 23p + 32 + χ(-1) + 2χ(2))/p^2.

A limit of 11 would extend the triangular increment by one proved step and
would still not be an all-depth ceiling. A limit strictly above 11, or any
single prime whose exact expectation exceeds 11, would kill
1+k(k+1)/2 as a universal upper bound. A limit strictly below 11 would kill
it as a description of the expectation. Either closed form is a finite
character-sum or point count; it does not require a depth sweep, a factoring
run, or a survival-conditional simulation. Until that identity exists, this
acquisition rule has no proved advantage over the paid √p control, and the
residual formula by itself is not a mechanism.

Verified end-to-end factoring improvement: NONE.
