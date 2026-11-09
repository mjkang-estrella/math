# W005 A — independent point, reduction and ECM audit

2026-10-08. **Review recommendations only; parent decides acceptance.**
New deductions here remain unaccepted pending that disposition.
**Verified new end-to-end factoring improvement: NONE.**
Symbolic mathematics and primary-source reading only; no mathematical execution,
numerical tests, point search, Lean, solver changes or delegation.

The map, four obvious torsion points, genus-three cover, literal valuation
obstruction and proposed quartic invariant survive. The moving-trace section
is **infinite order over Q(r)** for every fixed rational s>2t>0. Nevertheless,
its smooth reduction is the multiplicative element **4**, so scalar-order
factor detection on this section reduces to a base-4 p−1 computation.
The square obstruction needs a scope correction for multiples. The separate
fixed-u quartic genuinely removes both coordinate-square searches, but still
owes the trace congruence and field-square target; its ECM interpretation fits
existing Montgomery full-two-torsion constructions, with no new supply law.

## 1. Scope and hypotheses

I assessed the complete frozen W005 brief and point-development note, and
the predecessor material supplied verbatim in the task. I read all four
required instruction/specification files and README. STATE was context only:
its opening 155 and final 100 lines were read explicitly; its stale W004 status
does not override the supplied accepted disposition or this assignment.
Only this report and its assigned prefix were written. Original reports,
shared STATE, registries, harness and Lean are unchanged by this reviewer.
Exact snapshots, hashes, inspected primary passages and access limitations are
in the [scope ledger](W005-point-validation-evidence/read-scope.md).

Throughout, N is on the inherited branch gcd(N,30)=1; R is a unit square
modulo N; t=2R, s≡5R (mod N), s>2t>0, and Delta=s²−4t² is nonsquare.
Rational reduction means reduced denominators coprime to N. Write A_N for
this localization, and h for numerator/denominator bit length. Generalized
coefficients need their stated additional unit conditions. A generic section
theorem does not certify every rational specialization, including the
prescribed N-dependent one.

## 2. Birational map and the obvious subgroup — recommend acceptance

With s_j=s+b, direct expansion gives

    a=(b²−Delta)/4,  c=−(b²+Delta)/2,
    f(X)f(s_j−X)=z⁴+c z²+a²,  z=X−s_j/2.

The substitution x=2(W+z²)+c, y=2zx gives

    y²=x[(x−c)²−4a²]=x(x+b²)(x+Delta).

Conversely z=y/(2x), W=(x−c)/2−z² on x≠0 recovers the quartic.
The hypotheses b Delta(b²−Delta)≠0 make both smooth projective models
genus one. Their birational map extends across the omitted points. Precisely:

- infinity with W/z²→+1 maps to O;
- infinity with W/z²→−1 maps to (0,0);
- (z,W)=(0,a) maps to (−Delta,0);
- (z,W)=(0,−a) maps to (−b²,0).

For the second infinity, x=b²Delta/(4z²)+O(z⁻⁴) verifies the extension.
Thus these four points generate exactly E_b[2], with the first infinity
chosen as origin. They cannot generate a new point. This says nothing about
the full Mordell–Weil group. Here a≠0 follows from b²≠Delta.

## 3. The section — valid and generically infinite order

For b=t(r−r⁻¹), w=t(r+r⁻¹), P=(4t²,2tsw), the three cubic factors at P
are (2t)²,w²,s². Hence P lies on E_b; its ordinate is nonzero for real
nonzero r under these hypotheses. Exclude r=±1 and singular fibers.
The inverse formulas in the brief, including their factorizations, are correct.
For r>1, X>0, and Y>0 exactly when 1<r<d_+/d_−, where d_±=s±2t.
At either endpoint Y=0. Positivity is only a necessary lift condition.

**Symbolic order proof, not a numerical specialization.** Fix any rational
s>2t>0 and consider the local parameter r−1 over Q. At r=1 the cubic has
split multiplicative reduction after adjoining k=sqrt(Delta):

    y²=x²(x+Delta),   P_0=(4t²,4t²s),   q(P_0)=y/x=s.

P_0 is smooth. On the smooth nodal group use lambda=(q+k)/(q−k).
Its value at P_0 is (s+k)/(s−k)>1 in the real embedding with k>0.
It therefore has infinite multiplicative order. Specialization on the smooth
group is a homomorphism, so a torsion section would specialize to torsion,
a contradiction. This proves P has infinite order over Q(r), and also over
the generic Q(s,t,r). This proof uses a symbolic singular fiber, not a single
numerically tested smooth curve. The smooth-model group fact is documented in
[Lichtenstein §§4.1.7–4.3.2](https://virtualmath1.stanford.edu/~conrad/mordellsem/Notes/L11.pdf).

**Saved computation:** a rational norm point is produced by a fixed number of
rational operations after choosing the new trace. For K=Ns²+1 its height is
O(log N+h(s)+h(t)); construction and checks have polynomial bit cost at that
width. K and K+N are both 1 modulo N, so the claimed unit conditions on
r=(K+N)/K hold. The literal interval check reduces to
N/(Ns²+1)<4t/(s−2t), valid for the inherited integer s>2t≥4.
This does not find a point on the previously fixed second-trace curve.
Generic infinite order establishes a genuine section, not useful rational
square lifts or a bit-cost bound for its specialized multiples. Exact rational
scalar arithmetic must pay growing numerator/denominator lengths.
Retaining W004's reference first-field setup still pays O(N n²) time and
O(N n) working bits for its two-list Norm2, n=bitlength(N). These new
formulae do not remove that acquisition cost or replace its output law.

## 4. Intrinsic bad reduction, and a stronger computational identification

The proposed invariants are correct:

    c4=16(b⁴−b²Delta+Delta²),
    D_E=16 b⁴Delta²(b²−Delta)².

For p|N, b∈p A_N and Delta≡9R² is a unit. Thus c4 is a unit,
v_p(D_E)=4v_p(b)>0, and v_p(j)=−4v_p(b)<0. The equation is minimal
at p: a nonminimal integral rescaling would make v_p(c4)≥4. In particular
this is intrinsic split multiplicative bad reduction, not a removable defect
of the displayed model. A good integral model would have integral j.

Modulo p the node is (0,0), with tangent lines y=±kappa x, kappa=3R.
For its normalization,

    x=q²−kappa²,  y=q(q²−kappa²),
    lambda=(q+kappa)/(q−kappa),
    x=4kappa² lambda/(lambda−1)².

Exclude q=±kappa, the two branches over the node; q=infinity gives O and
lambda=1. This identifies the smooth group with F_p^*. To check the law
directly, a line y=m x+n cuts parameters satisfying
(q−m)(q²−kappa²)−n=0. Evaluating at ±kappa shows the product of their
lambdas is one. Negating y inverts lambda, exactly the chord-and-tangent law.

**Stronger consequence:** on every intended r≡1 branch, q(P)≡s≡5R,
so lambda(P)=4. Therefore lambda([k]P)=4^k. On finite charts with
4^k−1 nonzero modulo p, the quartic inverse gives

    X_k/R=(4·4^k−1)/(4^k−1),
    Y_k/R=(4^k−4)/(4^k−1).                            (1)

For scalar M, [M]P reduces to O exactly when 4^M≡1 (mod p).
This primewise detection is available directly through gcd(4^M−1,N):
binary exponentiation costs O(log M) modular multiplications, plus a gcd,
with O(log N)-bit residues. This replaces the rational-curve computation
for that detector. It is the p−1 mechanism at base 4, not random elliptic
orders; gcd=N still needs the ordinary proper-factor recovery analysis.
Intermediate affine denominators can detect additional coincidences, but
their smooth-group conditions likewise have explicit multiplicative images.
No equality of all possible denominator valuations is asserted. Points on
other components or reducing to the node are outside this smooth analysis.

This also **corrects the scope** of the parent's nonsquare-5 warning: X≡5R,
Y≡0 holds for the displayed section P(r), not every [k]P. Formula (1) is
the required replacement test for its multiples. For example, as a symbolic
scalar identity, k=3 gives X_3/R=85/21 and Y_3/R=20/21; their square
conditions involve the classes 17 and 105. They do not force the class 5
to be square: in Q(sqrt(17),sqrt(105)) both are squares and 5 is not.
This is a square-class counterexample to that algebraic implication, not
a finite-field numerical test or a claim of useful prime/input supply.

## 5. Simultaneous cover and quotient symmetry — recommend acceptance

The equations A²=F_A(r)=r(r+1)(d_+r+d_−),
B²=F_B(r)=r(r−1)(d_+−d_−r), with A=2ru and B=2rv, are exact.
For s>2t>0 their six branch places are exactly those listed by the parent.
Each radicand has a simple zero absent from the other, proving independence
in the geometric function field. At 0 and infinity their ratio is a local
unit and hence a square over the algebraically closed residue field, so
the inertia group there has order two. All six places contribute two;
Riemann–Hurwitz gives 2g−2=−8+12=4, hence g=3.

The three sign quotients are the two cubics and

    C²=(r²−1)(d_+r+d_−)(d_+−d_−r),  C=AB/r.

Each has four distinct branch points and a rational branch point, hence is
an elliptic curve after an origin is chosen. The identity
F_A(−1/r)=F_B(r)/r⁴ is correct. On the full cover it extends to the
involution (r,A,B)↦(−1/r,B/r²,A/r²); on u,v it sends (u,v) to (−v,−u).
It interchanges the two tests; it does not remove either. The three quotient
pullbacks give the usual isogeny from their product to the genus-three
Jacobian (their distinct sign eigenspaces exhaust the three differentials).
An isogeny of Jacobians is not a rational-point parametrization of the cover.

A precise partial alternative is to generate a point (r,A) on the first
quotient and test F_B(r) for a rational square. That removes the first test,
but no nontrivial seed, finite-index generators, height bound or success law
for this quotient has been supplied. Its visible branch points alone are
two-torsion. A bounded rational-r scan with numerator/denominator ≤H costs
O(H² poly(log N+log H+h(s))) for the two tests; no useful cap is proved.
The materially different fixed-u operation in §7 removes both tests instead.

## 6. Local obstruction, repair, and the root circularity

For any p|N and r≡1, X is the unit 5R modulo p. A rational u satisfying
u²=X is automatically p-integral (indeed a unit), so nonsquare 5 excludes
such u. This is not merely a restriction imposed by a chosen denominator
convention. For the literal K=Ns²+1, r=1+N/K,

    v_p(Y)=v_p(r−1)+v_p(d_+−d_−r)−v_p(4r)=v_p(N),

because d_+−d_−r≡4t is a unit. An odd exponent of any prime in N
therefore rules out a rational v. In particular every inherited squarefree
composite fails this literal lift. Squareful N with all exponents even is
not thereby successful; rational squareness is global.

The proposed change r=1+tN²/K² gives exactly

    Y=(tN/K)² H_K,
    H_K=(1−d_−N²/(4K²))/(1+tN²/K²).

For unit K, H_K≡1 (mod p), so v_p(Y)=2v_p(N). In fact H_K is a
square in every Q_p with p|N, by odd-prime Hensel lifting. Thus this
removes the local Y obstruction, not just its parity symptom. It need not
be a square in Q. Positivity requires K²>d_−N²/4, equivalent here to
the stated interval; checking this and all units is still necessary. X's
local class remains 5R. Imposing H_K=h² explicitly leads to

    z²(4t h²+d_−)=4(1−h²),  z=N/K,

a bidegree-(2,2) genus-one equation on its smooth model, with only the
trivial z=0,h=±1 points immediately supplied. Its required nonzero rational
point, z's valuation and the X lift remain unpaid. This identifies the
exact remaining equation rather than declaring the original parity failure
an impossibility for all modifications.

**Other residues with the same trace do not fix this section.** For unit r,
b≡0 (mod N) implies r²≡1 (mod N). At each odd prime power dividing N,
r is +1 or −1: the two choices give (X,Y)≡(s,0) or (0,s).
Mixed signs can already be split using gcd(r−1,N). Hence simply replacing
the r≡1 residue by another trace-compatible one cannot remove a nonsquare-5
obstruction for P(r). A genuinely different residue drops the common-trace
condition and requires a new packet/reduction proof.

With t=cR, s≡(1+c²)R and a known rational a²=1+c², the circularity
statement is correct **if a is a modular unit**: any displayed-section
lift u²=X on r≡1 gives (u/a)²≡R. On r≡−1 use v/a instead. Require
c, c²−1 and a to be units, as well as all denominators; c²−1 handles
distinct modular roots. The explicit parametrization
c=2h/(1−h²), a=(1+h²)/(1−h²) makes a known without a root oracle,
but does not produce u. It removes the constant obstruction while making
the remaining lift already sufficient for the desired modular root. This
is a one-way reduction for prescribed unit witnesses, not a hardness proof.
Here **s=(1+c²)R must mean a modular coefficient condition** if the
quadratic-field mechanism is retained: literal rational equality makes
Delta=(c²−1)²R² a square and f split over Q. Taking a lift
s=(1+c²)R+N L can avoid that failure, but nonsquare Delta, positivity and
the required sum-of-two-squares anchor must be constructed and checked anew.
For this generalized nodal family the same argument gives lambda(P)=c²
using kappa=(c²−1)R; varying c here supplies p−1 bases, not good curves.

## 7. The distinct fixed-u curve — good reduction and a concrete escape

Fix u and D=f(u²)≠0. The different genus-one curve

    C_D: Z²=D(v⁴−s v²+t²)

has the explicit point (v,Z)=(u,D). Its branch polynomial is separable
when t Delta≠0. At p|N it has good reduction provided u is p-integral
and D is a p-unit: the branch points are ±sqrt(R),±2sqrt(R), four
distinct points. The square root of R is used only to describe the geometry;
it is not given to a solver. Nonunit D requires its own gcd/degeneracy branch.

One Jacobian model is

    J_D: eta²=xi(xi+D(s+2t))(xi+D(s−2t)).             (2)

This follows by twisting the even-quartic Jacobian by D; over sqrt(D) the
curve is Z'²=v⁴−s v²+t². Equivalently (2) is the standard two-isogenous
curve of eta²=xi(xi²−Ds xi+D²t²). Computing c4 and discriminant in (2)
gives 16D²(s²+12t²) and 256D⁶t²Delta², respectively, hence

    j(C_D)=16(s²+12t²)³/(t²Delta²)
           ≡4·73³/81 (mod p).                      (3)

The proposed invariant is correct. It is independent of D, u and any
lift of s retaining s≡5R. These reductions range through **at most two
quadratic twist classes**, and at most two elliptic group orders per p;
neither class is asserted to occur under the chosen u law. This remains
an upper bound at exceptional j. Among p∤30, j=0 only at p=73, and
j=1728 only at p=7,17, since

    j−1728=4(5·7·17)²/81.

All twists at these j number gcd(6,p−1) or gcd(4,p−1), respectively:
the coefficients in y²=x³+b and y²=x³+a x are classified modulo sixth
and fourth powers. But varying D here gives only quadratic twists, not all
of them. At p=7 those two even
coalesce (a quadratic twist of y²=x³+a x is isomorphic when p≡3 mod 4).
Thus a blanket statement of exactly two classes would be incorrect.

For t=cR, s≡(1+c²)R, the cross-ratio and invariant become

    ell=((c−1)/(c+1))²,
    j_c=16(c⁴+14c²+1)³/[c²(c²−1)⁴].                (4)

These require c(c²−1) to be a unit. Varying c can genuinely vary the
geometric curve; varying only the lift of s cannot do so modulo p.

**Concrete operation avoiding the two square searches:** keep u fixed and
perform group operations on C_D itself. Both X=u² and Y=v² are then
squares by construction; choose the new trace s_j=u²+v² afterward. Unlike
the norm quartic's four two-torsion points, the two sign points (u,±D)
generically have a difference of infinite order. Here is a symbolic proof
and an explicit lower-cost ECM interface. The degree-two map

    (v,Z)↦(U,V)=(v²/t, vZ/t)
    M_D: B V²=U³+A U²+U,
    A=−s/t,  B=1/(Dt)                              (5)

is well defined on the smooth completions. Its known image is
Q=(u²/t,uD/t). Over Q(u,sqrt(D)), scaling to the constant curve
Y²=x(x²−s x+t²) sends Q to (u²,u sqrt(D)). A torsion point on a
constant elliptic curve in characteristic zero has constant coordinates
over the algebraic closure of the constant field. Since u² is nonconstant,
Q is not torsion over Q(u). With (u,D) as origin on C_D, subtracting
Q from (5) makes it an isogeny; (u,−D) then maps to −2Q. This proves
the asserted generic infinite-order difference without a numerical example.
It does not certify every chosen rational u.

For packet use, the remaining condition is **u²+v²≡s (mod N)**,
besides distinct valid second field, actual ordinary field-square target
and valid denominators. The displayed seed has trace 2u² and need not
satisfy it. Group operations on C_D need not preserve it either. Selecting
u from the paid original sum-of-two-squares anchor supplies a point with
trace exactly s, but that is the coincident-field case. Producing a different
useful point with the prescribed trace still has no charged success law.
Thus this operation really removes a representation failure, while moving
the missing computation to an explicit congruence/field-square filter.
Rational candidate generation must pay its actual growing heights; the
generic-order proof supplies no input-specific height or useful-hit bound.

For ECM use, (5) bypasses that packet filter entirely. Its modular setup
uses polynomial bit work and its scalar M uses O(log M) modular group
operations at O(log N)-bit width, plus all gcds and curve retries. It is a
degree-two **isogenous quotient**, not a birational identification with (2);
its invariant is 256(s²−3t²)³/(t⁴Delta), generally different from (3).
The isogenous curves have the same order over each good finite field, so
this change supplies efficient arithmetic, not an independent order sample.

## 8. Primary ECM prior art and final scoped recommendation

In (5), the generalized modular coefficients give A=−(c+c⁻¹), exactly
Montgomery's full-two-torsion parameter A=k+k⁻¹ with k=−c. This forces
three rational two-torsion points on that modular curve; it does not force
Suyama's three-torsion or the extra four-torsion of B=A+2. For arbitrary
lifted s these stronger statements over Q cannot be inferred from reduction.

[Montgomery 1987, §§10.3.1–10.3.2, pp.260–263](https://www.ams.org/journals/mcom/1987-48-177/S0025-5718-1987-0866113-7/S0025-5718-1987-0866113-7.pdf)
already gives point-bearing full-two-torsion curves, the A=k+k⁻¹ selection,
stronger torsion selections and x-coordinate arithmetic. His square-triple
construction also contains P itself: choose the three squares (2t)²,w²,s²
and translate x to remove the quadratic term. Thus neither having this
explicit point nor the variable-c full-two-torsion ECM mechanism is new
at that scope. This is not an asserted isomorphism to Suyama's family.

[Bernstein–Birkner–Lange–Peters, 2009-12-29, §7, pp.27–29](https://eecm.cr.yp.to/eecm-20091229.pdf)
provides explicit positive-rank families with larger torsion, including its
own Edwards translation, and discusses height growth. These are concrete
alternative point constructors if ordinary ECM is the intended operation.
Their existence gives no smooth-order or packet-lift law for this N,R stream.
[Barbulescu et al., 2012, introduction](https://arxiv.org/html/1202.4285v1#S1)
confirms that studying such parameter families and torsion divisibility is
an established ECM question; no theorem from its later sections is imported.

Recommend scoped acceptance of the birational identities, obvious subgroup,
generic infinite-order proof, genus-three description, exact local failure,
local repair and corrected good-quartic invariant/twist analysis. Narrow the
nonsquare-5 claim to its section/residue domain; use (1) for multiples.
The decisive remaining work is either a charged useful trace/field-square
filter on §7's rational points, or a specific ECM family selection claim
stronger than this known construction. No favorable point, congruence or
smooth-order distribution is established. No candidate was run. The saved
point/coordinate searches do not yet imply any end-to-end improvement.
