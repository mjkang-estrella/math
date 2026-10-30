# Positive coefficients and allowed poles do not force positive fractions

29 October 2026 UTC. Research-method obstruction only, credit 0.
BBK Conjectures 5.1 and 5.4 remain unresolved. Counts 3 additional / 33 total.
This report does NOT give a counterexample to any literal BBK product.

## Motivation and exact scope

The earlier root lane gives a finite exact LP criterion for BBK5.4, and the
Sol r5 lane rules out adaptive additive single-factor cancellation trees.
A possible replacement would first prove coefficient positivity of G, then
deduce its positive fractions from the simple allowed poles and reciprocal
symmetry. The explicit construction below rules out that generic implication,
even with strict integer coefficient positivity, constant coefficient 1,
the same allowed denominator Q, and the same degree/reciprocity data as one
literal BBK parameter pair. The BBK consecutive-product numerator is NOT
reproduced. Its special structure remains available and essential to any
argument not using additional hypotheses.

## 1. An explicit periodic sequence

Let L=105=3*5*7. For p in {3,5,7} set

    b_p(r)=0 if 2r+1=0 modulo p, and b_p(r)=1 otherwise;
    f(r)=1 if b_3(r)=b_5(r)=b_7(r), and f(r)=0 otherwise.

These definitions extend to all integer r and are 105-periodic. All three
binary patterns occur independently by the Chinese remainder theorem.
There is one residue with all b_p=0 and 48 with all b_p=1; hence sum f=49
over a period, f(0)=1, and f(-1-r)=f(r).

For any three binary values a,b,c, exactly

    2*1_(a=b=c) = 1_(a=b)+1_(b=c)+1_(c=a)-1.              (1)

Thus f is a signed sum of functions with periods 15,35,21 and 1. Its rational
generating function F(q)=sum_(r>=0) f(r)q^r has only SIMPLE poles at roots of
unity of orders dividing 15,21 or35. There is no primitive105 pole.
Writing P(q)=sum_(r=0)^104 f(r)q^r, F=P/(1-q^105), and P is palindromic
of degree104. Consequently F(q^-1)=-q F(q).

## 2. A necessary inequality for nonnegative short-period fractions

Suppose a rational function has an eventually105-periodic coefficient
sequence g and a representation

    sum_(d=1,3,...,35) z_d(q)/(1-q^d),                   (2)

with nonnegative real polynomial numerators. For indices beyond all numerator
degrees, its coefficients equal sum_d u_d(r), where each u_d is a
nonnegative d-periodic function (sum numerator coefficients by residue).

Average the equality along r+105j, over a common finite full period of all
the u_d. The left side stays g(r), while u_d becomes a nonnegative function
v_d depending only on r modulo gcd(d,105). Each such gcd is a proper divisor
of105, so v_d depends on at most TWO of the CRT coordinates modulo3,5,7.
This averaging is exact and finite; taking r sufficiently large removes
all finite initial exceptions. It does not assume the numerators have the
earlier root degree bound.

Restrict each CRT coordinate to two representatives: (p-1)/2 for binary0
and 0 for binary1. The eight resulting residues and signs are

    (000):52,-1; (001):7,+1; (010):10,+1; (011):70,+1;
    (100):87,+1; (101):42,+1; (110):45,+1; (111):0,-1.

Every nonnegative function of at most two coordinates has nonnegative signed
sum on this cube. Indeed, summing signs over a missing coordinate gives
0 when the other two values coincide and 2 when they differ. For functions
of fewer coordinates, sum again. Applying this to every v_d proves the
necessary inequality

    g(7)+g(10)+g(70)+g(87)+g(42)+g(45) >= g(52)+g(0).    (3)

The argument also works for any finite collection of periods none divisible
by105. This extension is not needed for the stated denominator set.

For g=f, the left side is0 and the right side2. Thus F has nonnegative
integer coefficients and only allowed simple poles but admits no (2).
This first example has zero coefficients; the next removes that limitation.

## 3. Strictly positive coefficients and matching reciprocal degree

Set S=3570=34*105, D=S-1=3569, and

    J(q)=(1+q^S)*(3F(q)+1/(1-q)) -3 +3q^D.              (4)

Every Taylor coefficient of J is a positive integer. The constant is
4-3=1. For 1<=r<S the coefficient is 3f(r)+1, with an additional3 at r=D.
For r>=S it is 6f(r)+2. In particular the eventual sequence g is strictly
positive, taking values2 and8. Its signed sum in (3) is 12-16=-4. Therefore
J admits NO decomposition (2), with arbitrary finite numerator degrees.

Both F and 1/(1-q) transform to -q times themselves under q->q^-1.
The factor 1+q^S and the antisymmetric polynomial -3+3q^D therefore give

    J(q^-1)=-q^-D J(q).

Let Q=product_(d=1,3,...,35)(1-q^d), of degree324. By (1), QF is an integer
polynomial: all reduced cyclotomic denominator factors of F occur in Q,
and division is integral by monic polynomial division (up to leading sign).
Thus N=QJ is an integer polynomial. At infinity J~-q^D, because the
leading -4q^D from the first term of(4) is changed to -q^D by +3q^D.
Hence N has degree3893, constant1, leading coefficient-1 and is
anti-palindromic. These are exactly the denominator, degree, leading/constant
signs, and reciprocal exponent of BBK G(107,17):

    deg numerator = 17*(2*107+17-2)=3893,
    D=2*17*(107-2)-1=3569.

The numerator N is NOT product_(i=0)^16(1-q^(213+2i)). No claim about that
literal product is made. Matching these invariants merely shows why they
cannot replace its special factorization in a proof of5.4.

## Verification and limits

check.py enforces 512MiB/30CPU-second/BLAS1 limits. It verifies(1) and
reciprocity on all105 residues, all relevant gcd-fibre sign inequalities,
the eight CRT representatives, signed value-4, exact polynomial division
QF, and all degree/reciprocity/leading coefficients of N. The full polynomial
identity is checked by exact cross multiplication. The generic impossibility
proof is the all-degree averaging argument above, not an inference from a
finite LP solver. No floating point or larger BBK grid is used.

Actual BBK v1 HTML was opened again on29October, especially Section5/5.4;
its polynomial-numerator reading remains the earlier documented convention.
No new comprehensive registry search or novelty clearance is claimed.
This is an elementary method obstruction, not a discovery nomination,
formalization, paper or change of campaign credit. Next work on5.4 must use
more than positivity, poles and reciprocity; simultaneous product structure
or a source-specific positive construction remains unproved.
