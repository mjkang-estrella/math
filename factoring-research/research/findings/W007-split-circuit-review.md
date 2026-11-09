# W007 split-circuit symbolic review

2026-10-08. Independent T3 child review of the frozen W007 brief. No recursive
delegation, candidate execution, polynomial search, dependency installation,
shared code/Lean edit, registry change, commit or publication. The owned source
directory is `W007-split-circuit-review-sources/`; its input manifest identifies
the seven instruction/state/brief snapshots. Current STATE still principally
describes W006; this task's explicit W007 brief governs this distinct review.

**Disposition:** the displayed P3 factorization, characteristic-zero branch
values, full order-128 geometric and arithmetic groups, constant field Q, and
Galois-closure genus **25 are correct**. Below is a direct proof, rather than an
application of a theorem about iterates of one fixed polynomial. Both adaptive
identities are correct over odd finite fields. Candidate A's rejection is
correct, with the prime-power qualification made explicit. **Verified new
factoring complexity improvement: NONE.** No nonzero fourth split-fiber value
has been obtained or excluded.

## 1. Exact factorization and its finite-field scope

Write Q=X^2-X. Then P2=Q(Q-2), and

    (X+4/5)(X-9/5) = Q-36/25,
    (X+2/5)(X-7/5) = Q-14/25,
    (Q-36/25)(Q-14/25) = Q(Q-2)+504/625.

This proves the proposed P3 factorization without a search. In particular
Q(-4/5)=36/25 and P2(-4/5)=-504/625. Its eight roots have common-denominator
numerators {-5,0,5,10,-4,9,-2,7}, with denominator 5. They are distinct over Q.
Every nonzero numerator difference has absolute value at most 15. A prime
greater than 13 is at least 17, so none divides a difference or the denominator.
P3 therefore has exactly eight distinct roots over every such F_p.

The alternative fiber is also exactly as stated:

    P2-24=(Q-6)(Q+4)=(X-3)(X+2)(X^2-X+4).

The last factor has discriminant -15, so this alternative gives exactly six
rational roots after adjoining the old four. It refutes automatic rational
doubling, but does not preclude splitting of that quadratic over individual
finite fields.

For later use set

    u=X-1/2,  A=5/4,  B=373/625,  C=(252/625)^2=63504/390625.
    F(u)=((u^2-A)^2-B)^2-C = P3(u+1/2).

These are three possibly different quadratic maps in succession. The original
recurrence is f2 composed with f1 composed with f0, where
f0(Y)=Y(Y-1), f1(Y)=Y(Y-2), and f2(Y)=Y(Y+504/625).

## 2. Branch locus and inertia over characteristic zero

Direct differentiation gives

    F'(u)=8u(u^2-A)((u^2-A)^2-B).

Its seven zeros are distinct: A and B are nonzero, and
A^2-B=9657/10000 is nonzero. The critical values are

    b2=-C                         = -63504/390625,
    b1=B^2-C                      = 121/625,
    b0=(A^2-B)^2-C                = 123201/160000.

Their differences include

    b1-b2=B^2,
    b0-b2=(A^2-B)^2,
    b0-b1=A^2(A^2-2B)=3689/6400.

All three are nonzero. At b2 there are four simple critical points, hence
four ramified points of index 2 in the degree-eight cover. At b1 there are
two such points; at b0 there is just u=0. There are no other finite critical
values. Infinity is totally ramified of index 8 because F is a polynomial of
degree 8.

Consequently the inertia generators, acting on the eight roots, have cycle
types respectively

    b2: 2^4;   b1: 2^2 1^4;   b0: 2 1^6;   infinity: 8.

In the Galois closure the finite inertia groups are cyclic of order 2, and
the infinite inertia group is cyclic of order 8. Four simultaneous critical
points over b2 do NOT give inertia (C2)^4 at a single place: one local loop
performs all four swaps. Characteristic zero is tame, and an inertia element's
order is its permutation order in this faithful root action. Normal closure
introduces no branch values away from the branch locus of the original cover.

As a consistency check, the degree-eight cover itself has total ramification
contribution 4+2+1+7=14, so its Riemann--Hurwitz equation is -2=-16+14, as
required for its source P1.

**Reduction caution:** the earlier assertion about eight roots at T=0 does not
assert good reduction of this entire branch configuration. For example,
b0-b1=7*17*31/6400 vanishes modulo 17, although 17>13 and all eight roots of
P3 remain distinct modulo 17. The following group/genus proof is over Q and
its algebraic closure; it is not transferred to every p>13.

## 3. Direct proof of the full geometric group

Work over k=Qbar and use T as a transcendental parameter. Intermediate values
give a rooted binary tree of depth three:

    tau^2=T+C,
    v^2=B+tau,       w^2=B-tau,
    r^2=A+v, s^2=A-v, t^2=A+w, h^2=A-w.

The eight u-roots are +/-r, +/-s, +/-t, +/-h. Every root automorphism preserves
this tree, so the geometric group G embeds in its automorphism group

    W3=(C2)^4 semidirect W2,   W2=(C2)^2 semidirect C2,
    |W3|=2^(4+2+1)=128.

This embedding alone is only an upper bound. To prove equality, first take
the intermediate degree-four cover

    H(V)=(V^2-B)^2-C.

Its two finite branch values are b1 and b2. At b1, V=0 is its only ramified
point, so its geometric group G2 contains a single transposition within one
of the sibling pairs {v,-v}, {w,-w}. The cover is connected: for any nonconstant
polynomial H of degree four, [k(V):k(H(V))]=4, and H(V)-T is irreducible over
k(T). Thus G2 is transitive on its four roots and consequently on its two
sibling pairs. Conjugating the displayed transposition supplies the swap in
the other pair. The two disjoint swaps generate (C2)^2 in the kernel of the
action on the two pairs; the quotient acts transitively on two pairs and has
order 2. Since G2 is already contained in W2, |G2|=4*2=8 and G2=W2.

The splitting field of H(V)-T is contained in the splitting field of F(u)-T:
each V is u^2-A for the appropriate roots u. Restriction of these Galois
extensions is surjective, giving G -> G2 with kernel contained in (C2)^4.
At b0 only u=0 ramifies. Its inertia therefore exchanges just the two leaves
above V=-A and fixes every other leaf. This is one individual sibling swap
in that kernel. The quotient G2 is transitive on the four V-values. Lifting
its elements to G and conjugating supplies each of the four individual
sibling swaps. They have disjoint supports and generate all of (C2)^4.

It follows that

    |G|=16*8=128,  G=W3.

This proves the full group for these actual constants. It uses the separation
of b0 from b1,b2 to isolate the last transposition; it does not assume that
an arbitrary quadratic composition has full wreath monodromy.

## 4. Arithmetic group, constants and genus

Let L be the splitting field of P3(X)-T over Q(T), and let Q_const=L intersect
Qbar. Its arithmetic group also preserves the same tree because all three
maps have rational coefficients. It is therefore a subgroup of W3. The
geometric group just proved is its normal subgroup of order 128. Thus

    Gal(L/Q(T)) = Gal(L Qbar/Qbar(T)) = W3,
    Q_const=Q.

The second conclusion follows from the usual restriction exact sequence to
Gal(Q_const/Q): the arithmetic/geometric quotient is trivial. In particular
this is a regular extension of Q(T), not one secretly requiring a constant
quadratic or cyclotomic extension.

Let C_split be the smooth projective curve with function field L. Applying
Riemann--Hurwitz to its geometric degree-128 Galois cover gives

    2g(C_split)-2
      =128*(-2+(1-1/2)+(1-1/2)+(1-1/2)+(1-1/8))
      =48.

Therefore **g(C_split)=25**. The parent arithmetic was right, and the group,
constant-field and ramification premises are now proved explicitly. This is
the genus of the Galois closure, not of the original degree-eight source.

## 5. Meaning of a completely split rational fiber

Restrict to finite rational a outside {b2,b1,b0}. Over that open base the
cover C_split -> P1 is an unramified Galois cover, a W3-torsor. Then

    P3(X)-a has eight distinct rational roots
      iff C_split has a Q-rational point over T=a
      iff all 128 geometric points over T=a are Q-rational.

For a direct explanation, a point in the splitting cover records compatible
choices of all seven radicals in section 3. Rational coordinates make all
eight roots rational. Conversely eight distinct rational roots let one choose
the labels and recover tau, v, w and all four bottom radicals rationally.
The root action is faithful: no nonidentity specialization automorphism fixes
every root. Hence the specialization action is trivial precisely when the
torsor has a rational point. Since all deck transformations are defined over
Q and act freely transitively on an unramified geometric fiber, one rational
point then supplies 128, not just one. These are tree-compatible labelings,
not all 8! arbitrary root orderings.

The known fiber T=0 is unramified and gives the explicit rational tuple

    tau=252/625, v=1, w=11/25,
    r=3/2, s=1/2, t=13/10, h=9/10.

Changing compatible signs gives its 128 rational points. No claim is made
that these are all rational points on the projective curve.

Thus the precise fourth-stage gate is a rational solution of the seven
displayed equations with T nonzero and outside the branch locus. A rational
point merely on P3(X)=T proves only one rational root. The weaker choice
T=P3(r) does not solve the splitting-cover problem. If the full gate succeeds,
its eight new roots are automatically disjoint from the old ones because
T is nonzero; their distinctness is ensured by excluding the branch values.

A nonconstant rational one-parameter splitting formula would give an inclusion
L -> Q(z), hence a nonconstant morphism P1 -> C_split after smooth completion.
Riemann--Hurwitz rules this out, since -2 cannot equal a positive degree times
48 plus a nonnegative ramification contribution. This excludes such a formula
for the fixed full splitting data; it supplies no time lower bound.

Invoking the standard Faltings finiteness theorem also shows that this fixed
curve has only finitely many Q-rational points and hence only finitely many
completely split rational values. This is an external qualitative theorem,
not an effective enumeration or a height bound established here. The original
paper's bibliographic record was checked; its proof was not re-audited:
[Faltings, Invent. Math. 73 (1983), 349--366](https://link.springer.com/article/10.1007/BF01388432).
Neither finiteness nor genus decides whether there is a nonzero such value.
Varying earlier coefficients and seeking only finite-field splitting remain
different problems.

## 6. Anti-commuting determinant rejection

Block multiplication gives A_(j+1)^2=(S_j+t_(j+1)^2) I: the off-diagonal
blocks cancel because t_(j+1) is scalar. The trace is zero at the first level
and remains zero under the block construction. Over the generic rational
function field in the t_i, S_j is nonzero and A_j has eigenvalues +/-sqrt(S_j).
Its minimal polynomial divides the separable polynomial X^2-S_j. Trace zero
forces equal eigenvalue multiplicities 2^(j-1), proving

    det(XI-A_j)=(X^2-S_j)^(2^(j-1)).

Both sides are integral polynomial expressions in X,t_1,...,t_j, so equality
over that generic field proves the polynomial identity and all specializations,
including S_j=0 and reductions modulo composite N. No diagonalizability claim
is needed at a singular specialization.

For an integer value B0=X^2-S_j and m=2^(j-1), a prime power ell^e exactly dividing N
contributes ell^min(e,m*v_ell(B0)) to gcd(N,B0^m). The corresponding exponent
in gcd(N,B0) is min(e,v_ell(B0)). Their prime supports coincide. Therefore if
the powered gcd is proper and nontrivial, the unpowered gcd already is too.
For squarefree N the gcds are equal. With repeated primes the powered gcd
can instead become N and lose a proper unpowered gcd, so exact gcd equality
must not be asserted generally. A prime-power valuation gain gives no new
distinct root coverage.

Summing the squares and repeated modular squaring evaluates the determinant
in O(j) modular operations without a matrix. There are at most two roots over
an odd field, and at most one over F2. The rejection is sound. Distinct signed
sums for a commuting construction over Q do not by themselves ensure distinct
residues modulo unknown primes or cheap product evaluation. H029/H030's paid
product-acquisition obligation is unchanged.

## 7. Exact adaptive laws

Fix a polynomial as a function on F_p, with input uniform on the entire field.
Let mu(y)=Pr[P(x)=y], z=mu(0), and c=sum_y mu(y)^2. These are masses of sets of
inputs, not root multiplicities. A fresh independent uniform training input
r makes a=P(r) have law mu.

The zeros of P(x)(P(x)-a) are the union of the fibers at 0 and a. Those fibers
are disjoint unless a=0, giving exactly

    z'(a)=z+mu(a)-1_(a=0)*z,
    E[z'-z | P]=sum_a mu(a)^2-z^2=c-z^2.

If a=0, the polynomial is squared but its zero set does not grow. This zero
mass identity is valid in every characteristic.

For independent Y,W with law mu, the next collision probability is the
probability of Y(Y-a)=W(W-a). Over a field this is equivalent to

    (Y-W)(Y+W-a)=0.

In odd characteristic the two events Y=W and Y+W=a intersect only at
Y=W=a/2. Inclusion--exclusion therefore proves

    c'(a)=c+sum_y mu(y)mu(a-y)-mu(a/2)^2.

Equivalently c'(a)-c is the sum over y != a/2 of the nonnegative terms
mu(y)mu(a-y). The coefficient counts ordered pairs, so no factor 1/2 belongs
in the formula. In particular c <= c'(a) <= 2c, the upper bound following
from Cauchy--Schwarz on the convolution term. Under the actual training law,

    E[c'-c | P]
      =sum_(a,y) mu(a)mu(y)mu(a-y)-sum_a mu(a)mu(a/2)^2.

This depends on additive structure, not just on c and z. The identities
provide no equality asserting doubling or rapid growth.

In characteristic two the correct collision formula is instead

    c'(a)=c+sum_y mu(y)mu(a-y)-1_(a=0)*c.

Indeed the two events intersect on the entire diagonal when a=0 and are
disjoint when a!=0. Squaring is a bijection of a finite field of characteristic
two, so c'(0)=c, as this formula confirms. Over Z/NZ the zero-divisor equation
does not force either factor to vanish globally. These collision formulas
apply separately over each prime field; replacing the field by a composite
ring in their proof would be invalid.

For comparison, selecting a uniformly in F_p independently of P(r) would give
E[z'-z]=(1-z)/p, generally different from c-z^2. That is a different algorithm.
At saturation mu(0)=1, c=1 but local growth is zero. If both prime fields have
zero mass 1, every direct gcd is N. Saturation at just one prime can still
be useful when the other prime's zero mass is less than 1.

## 8. Proper factors and paid costs

For N=pq with distinct odd primes and any fixed eligible P, a fresh uniform
x modulo N has independent uniform CRT components. Hence the exact gcd laws
are

    Pr[gcd(N,P(x))=N] = z_p*z_q,
    Pr[proper nontrivial gcd] = z_p+z_q-2*z_p*z_q.

Conditioning on the full construction history still permits this law if x is
sampled freshly afterward. Averaging over adaptive histories gives the
expectation of that expression; it does not justify replacing E[z_p*z_q]
by E[z_p]E[z_q] after joint stopping or filtering. Training r itself is a
global root of the newly constructed polynomial, and remains one forever:
retesting planted inputs yields gcd N, not a factor.

There is also a useful exact one-stage check. Conditional on fixed local
polynomials, let delta_l=c_l-z_l^2 for l=p,q. If the next training input is
uniform modulo N with no subsequent conditioning on its outcome, its CRT
components are independent. For an independent test after that stage,

    E[proper-gcd probability after stage | current polynomials]
      =(z_p+delta_p)+(z_q+delta_q)
         -2*(z_p+delta_p)*(z_q+delta_q).

Thus increased local coverage can decrease separation. This conditional
identity is not a claim about a process selected by arbitrary stopping rules.

The explicit evaluator performs one multiplication and one subtraction per
stage. To construct j coefficients a_k=P_k(r_k) by the given prefix evaluator
for k=0,...,j-1 costs exactly sum_k k=j(j-1)/2 such pairs, plus training-input
acquisition. This is a paid O(j^2) construction, not an O(j) one. Afterwards
each test needs j pairs and a gcd. With n=bit_length(N), s fresh tests and
modular multiplication/gcd costs M(n), G(n), the arithmetic ledger is

    O((j^2+s*j)*M(n) + s*G(n))
      + parameter generation, constant reading/reduction, denominator
        gcd/inversion, randomness and control costs.

Coefficients can be stored as j residues using O(j*n) bits; each evaluator
uses reduced n-bit operands and at most 2n-bit multiplication temporaries.
Reading an explicitly supplied H-bit rational numerator or denominator costs
at least its actual input length, as does reducing it. Alternatively a short
modular circuit can generate its residue without expanding its enormous exact
integer value, but the circuit's construction and constants must be paid.
No bound on exact rational heights is silently substituted for that ledger.

Every denominator to be inverted is gcd-tested. A proper gcd is an early
factor; gcd N exhausts that parameter branch; a unit can be inverted at its
actual bit cost. Clearing a nonunit denominator and then treating the result
as the original rational evaluation is unsound. Random sampling and rejected
parameters also cost work. A supplied list of exponentially many explicit
roots carries its own output/verification cost even if the evaluator is short.

For this fixed P3, eligible primes have z_p=8/p, and the direct proper-gcd
probability is 8/p+8/q-128/(pq). This is fixed-degree coverage, not an
asymptotic density gain. A full gcd can sometimes be localized by evaluating
smaller known factors, but that is an additional specified computation. For
the fixed eight-factor example it is a constant list of linear tests. At
growing depth the factor-acquisition and localization program must be paid;
the norm label does not provide it. General composites additionally require
their prime-power handling and the project's complete splitting contract.

## 9. Bounded primary-literature check

The two supplied author-hosted PDF endpoints failed in the web reader. The
arXiv HTML versions were retrieved and their exact bytes and hashes retained
in the owned source directory. No factoring novelty or completeness of a
literature search is claimed.

Juul--Kurlberg--Madhu--Tucker, *Wreath products and proportions of periodic
points*, arXiv:1410.3378v1: section 2, Lemma 2.4 treats compatible root
labelings for a composition and supplies a wreath-product embedding. This
part is relevant here, but an embedding is not equality. Section 3,
Theorem 3.1 imposes critical-orbit separation and inertia-generation hypotheses
for iterates of one rational map. It does not directly assert the group of
this nonautonomous three-map composition or of future adaptive schedules.
The single-sibling inertia and conjugation proof above supplies the needed
equality for the actual W007 constants.
[Primary text, sections 2--3](https://arxiv.org/html/1410.3378v1).

Fried, *Variables separated equations: Strikingly different roles for the
Branch Cycle Lemma and the Finite Simple Group Classification*,
arXiv:1012.5297v5: section 5.1.2, equation (5.1), gives the permutation-index
form of Riemann--Hurwitz. Section 7.2.4 discusses wreath products for
compositions, including the need to determine which subgroup occurs. This
supports the method and cautions against inferring equality from decomposition.
No special classification theorem from that paper is imported into W007.
[Primary text](https://arxiv.org/html/1012.5297v5).

## 10. What can change the disposition

The selected symbolic gate is complete: genus 25 is justified, not refuted.
It closes a rational one-parameter formula for this fixed full splitting
cover. It neither closes the existence of a further split value nor establishes
any factoring lower bound. The elementary doubling counterexample and the
characteristic-two correction are explicit above; the p=17 branch collision
prevents an unjustified finite-field transfer.

The next decisive fixed-cover question is whether the explicit radical system
in section 3 admits a rational solution with T outside {0,b2,b1,b0}. A proposed
solution can be checked exactly at fixed degree with cost polynomial in its
supplied bit lengths. No unbounded point finder, point oracle or height bound
is supplied. An alternative finite exclusion certificate could settle this
fixed gate; a blind larger point search would not establish scalable supply.
One successful fourth-stage witness would still not be an all-depth generator.

For the adaptive mechanism the separate missing theorem is a paid bound on
the history-averaged separating probability relative to quadratic training
cost, including rejected branches and all failed trials. The two local
identities by themselves supply no such theorem. No numerical experiment,
shared implementation or Lean action is recommended solely by this review.
