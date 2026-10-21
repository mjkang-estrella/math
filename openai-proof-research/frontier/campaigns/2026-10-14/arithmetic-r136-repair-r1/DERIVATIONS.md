# Repair derivations — unchanged T054L136

These are auxiliary deductions for the first author response, not a replacement frozen theorem or a claim to have repaired its irrationality assertion. The frozen bytes were copied and checked before this development.

## 1. Correct local inputs and the precise surviving question

Both odd-prime reductions of a x²−(a+1)y²=n are negative squares. At p|a+1, a≡−1; frozen(ii) fails to obstruct when p≡3 (mod 4). If (n/p)=−1 there, (−n/p)=+1 and the nonzero root of a x²=n lifts with y=0 by Hensel. Local discriminant transport therefore transports solubility as well as obstructions.

At 3 the half-norm is x²+y² modulo 3. If 3 divides a nonzero represented n, both coordinates are divisible by 3, so v₃(n) is even. Genus equivalence transports this to every complement. At n=1, (ii) is impossible, so (i) excludes norm 2 in every complement. Nonsquare a(a+1) excludes isotropic vectors. These facts retain the finite-order-automorphism argument but do not establish a growing positive minimum.

The original linear bound E(B,a) is stronger than necessary. It would suffice that, for each fixed real C, some B_C makes every allowed a at every B≥B_C and every complement M satisfy μ(M)>C. This is the divergence of the infimum over all such a and M, not divergence for one chosen family. No such asymptotic assertion is established here.

## 2. A symbolic family with a norm-4 genus companion

Let z be any positive even integer and put

    a = 6z²+4z+1,
    N_a = <2a> ⊥ <-2(a+1)>,
    M_a = <4> ⊥ <-a(a+1)>.

The two identities

    a   = (2z+1)² + 2z²,
    a+1 = (2z)² + 2(z+1)²

show that every odd prime dividing a(a+1) satisfies (−2/p)=+1: in either identity the two coordinates have no common odd prime divisor. This holds irrespective of the valuation of p. At such a prime, the unit coefficient of N_a is congruent to −2 modulo p; the unit coefficient of M_a is 4. Their ratio has square residue −2. Hensel gives an exact square unit, which identifies these unit lines. Both determinants are −4a(a+1), so the remaining lines also identify, by scaling by the reciprocal square unit. At other odd primes both binary lattices are unimodular with equal determinant, hence isometric.

Write z=2t. Then a=24t²+8t+1≡1 (mod 16), since t(3t+1) is even. Put k=(3a−1)/2≡1 (mod 8), and choose s in Z₂* with s²=k. In N_a the vectors

    v=(2/s,1/s),
    u=(-(a+1)/(2s),−a/s)

are integral, have determinant −1, and satisfy

    v²=4,  (v,u)=0,  u²=−a(a+1).

Thus they form a Z₂-basis. Both real signatures are (1,1). Consequently N_a and M_a are in the same genus and have isomorphic finite discriminant quadratic forms. This proves the companion assertion for the whole polynomial family, without a squarefreeness assumption.

This alone does not make a satisfy the frozen prime-divisor or witness conditions. The next construction supplies infinitely many parameters satisfying them for one FIXED B.

## 3. Unbounded discriminant with fixed B=22 and μ=4

An exact seed is

    z₀=84, a₀=42673=139·307,
    a₀+1=42674=2·19·1123,
    a₀=199²+3·32²,
    x₀=3z₀+1=253, w₀=16,
    x₀²−18w₀²=59401=(3·199²−1)/2.

The odd factors displayed are prime. Primes 139 and 307 are 1 modulo 3. The witnesses for n=1,...,22, in order, are

    139i, 19ii, 19ii, 139i, 139i, 139i, 139i, 19ii,
    139i, 307i, 139i, 19ii, 139i, 19ii, 307i, 139i,
    307i, 19ii, 307i, 139i, 19ii, 19ii.

All relevant valuations are one. These finite symbol checks are reproduced in private/verify_mathematics.py.

Let

    U = [[17,72],[4,17]],
    L = 6·199·139²·307²·19².

The determinant of U is 1, so its reduction lies in the finite group GL₂(Z/L). There exists a positive r with U^r=I modulo L. No computation of this order or of its enormous powers is required. For j≥0 set

    (x_j,w_j)^t = U^(rj)(253,16)^t,
    z_j=(x_j−1)/3,
    a_j=199²+12w_j².

U preserves x²−18w² and has positive entries. Thus x_j,w_j and a_j strictly increase with j. Congruence x_j≡253 modulo 6 makes z_j a positive even integer. The preserved Pell equation gives

    a_j=(2x_j²+1)/3=6z_j²+4z_j+1.

The congruence w_j≡16 modulo 199 makes gcd(199,2w_j)=1. Since a_j=199²+3(2w_j)² is odd and prime to 3, every prime p|a_j satisfies (−3/p)=+1 and therefore p≡1 modulo 3. Indeed p cannot divide 2w_j, since it would then divide 199; primitivity excludes that case. This verifies the full prime-divisor restriction, not merely a≡1 modulo 3.

Also w_j≡16 modulo each of 139²,307²,19², hence a_j≡a₀ modulo each of those squares. The entire witness list and its valuation-one conditions persist. Therefore every a_j satisfies ALL frozen arithmetic hypotheses at B=22 (and at any fixed B between 2 and 22). Section 2 supplies the companion M_a_j. Norm 2 is excluded by the fixed witness 139 for n=1, and M_a_j represents 4, so μ(M_a_j)=4 exactly. The discriminants 4a_j(a_j+1) tend to infinity.

This is an infinite parameter sequence at FIXED B, not a sequence with B tending to infinity. It does not contradict an unspecified B₀, nor prove rationality of any cubic. In particular it supplies no license to dismiss the large-B problem or to conclude that the full theorem is false.

## 4. Actual same-T complements and the bounded-family obstruction

For each a_j, the unchanged Yang–Yu and generic-period construction supplies an exact-A cubic with scalar transcendental endomorphisms. The stipulated associated-K3 interface and the determinant/index calculation give a K3 S₀ with NS=N_a_j and its exact integral T. Glue M_a_j to that T using the opposite discriminant forms. Primitive unimodular gluing gives the K3 lattice of signature (3,19); retain the original period line in T. Period surjectivity gives a K3 with NS exactly M_a_j, because T_Q has no rational (1,1) class. The positive class makes it projective, and the integral transcendental Hodge structure and scalar endomorphisms are preserved. Thus these are actual same-T complements, not abstract forms that can be omitted from the test.

The norm-4 basis vector h is primitive and no root is perpendicular to it: an orthogonal vector is a multiple of the negative basis vector, of square −a(a+1)y², which cannot be −2. Here is the reflection step explicitly. Fix an ample A and choose the sign with h·A>0. If h is not nef, an irreducible curve C with h·C<0 must be a (−2)-curve: every nonnegative-square effective curve lies in the closure of the positive cone and has positive intersection with h. Reflect h to h+(h·C)C. This integral isometry preserves the positive-cone component and strictly decreases the positive integer A·h. Thus the process stops at a nef class. No root can be perpendicular to any resulting class, because the reflections are isometries and no root was perpendicular to the original h. A curve perpendicular to a nef positive class would have negative square by the Hodge index theorem, hence square −2 by K3 adjunction. There is no such curve, so the final class is ample by Nakai–Moishezon. Denote it again by h. The lattice has no isotropic vector and no norm-2 vector. Huybrechts Chapter 2, Corollary 3.15 makes h base point free: a fixed part would force an elliptic curve, contrary to anisotropy. Bertini and ampleness give smooth connected general members, of genus 3 by adjunction. Chapter 2, Theorem 2.7 gives the very ample class 3h, of square 36. Its Hilbert polynomial is 18m²+2 and h⁰(3h)=20. Thus all these surfaces occur in the fixed Hilbert scheme of that polynomial in P¹⁹, a bounded projective family. This argument does not require a quartic-embedding classification.

Consequently their unbounded discriminants coexist with a single bounded projective family and bounded-genus pencils. This specifically invalidates replacing the source's positive-square/pencil exclusions by a claim that discriminant growth alone excludes bounded families. It does NOT show that this bounded family is one of the source's particular marked diagram families or prove that a given source correction is nonzero. It only refutes a proposed general implication from large discriminant to those exclusions.

## 5. What the stronger compatible reductions do and do not buy

The source's bounded-MRC argument controls the square of a pushforward ample divisor, not determinant. Its marked-cover and embedded-field arguments use uniformly bounded genera of pulled-back pencils, not determinant. The fixed-B family above defeats the naive substitute at both interfaces. An alternative invariant must prove the needed exclusions for the actual uniformly bounded ordinary/log diagrams and covers, respecting all same-T complements, or construct a different invariant whose net value can still be forced to be nonzero. Choosing only a favorable complement removes the whole-block count justification: cancellation tracks integral T-classes, not a chosen NS representative.

For each fixed C one still has to prove exclusion for all sufficiently large B, or find another full-scope irrationality argument. The Pell construction preserves finitely many selected witnesses; it does not provide fresh witnesses for arbitrary n. Treating its discriminant growth as B growth would exchange quantifiers illegally. The exact unpaid operation remains this uniformly quantified arithmetic-to-geometric exclusion (or a complete replacement for it).

## 6. The original diagonal lattice already has exact minimum 2a

This removes a potentially distracting residual: small vectors are a complement/genus problem, not a failure to bound the particular diagonal NS constructed from X. For every positive integer a, without either frozen witness condition,

    μ(<2a> ⊥ <-2(a+1)>) = 2a.

Proof. Suppose n=a x²−(a+1)y²>0 with integers x,y. Changes of signs let x>0 and y≥0. If y≤2a x/(2a+1), set k=x−y≥1. Then y≤2ak and

    n=a k²+2aky−y² ≥ a k² ≥ a.

If y>2a x/(2a+1), apply the integral isometry

    x'=(2a+1)x−2(a+1)y,
    y'=−2a x+(2a+1)y.

It has determinant 1 and preserves the half-norm. We have y'>0. Positivity of n gives y/x<sqrt(a/(a+1))<(2a+1)/(2(a+1)), so x'>0. Moreover y/x>2a/(2a+1)>a/(a+1), so x'<x. Repeat; the strictly decreasing positive integer x forces termination in the previous case. Thus all positive represented n satisfy n≥a, and (x,y)=(1,0) attains a.

Consequently the author §3 assertion would be easy for the particular N_a alone. It cannot be transferred from that global minimum to all members of its genus: the explicit M_a above has minimum 4. Local isometries preserve local representability, not the integer minimum in each global class. Restricting the test to only N_a would exclude permitted whole centers; the source's integral-T block count supplies no net count for that restriction. No such restriction is adopted.

## 7. Arbitrarily long witness lists do not repair the sign locally

Here is a quantified compatibility construction, separated carefully from an actual genus counterexample. For EVERY fixed B≥2, infinitely many frozen-allowed a can be constructed such that:

* a≡1 modulo 16;
* every prime divisor of a splits in Q(√−2);
* all explicitly selected witnesses on the a+1 side also split in Q(√−2);
* the half-norm equation with n=2 is soluble at 2, 3, every prime divisor of a, and every selected a+1 witness.

For each 1≤m≤B outside the squareclasses 2 and 3, choose a distinct prime p_m>B with

    (−2/p_m)=(−3/p_m)=+1,   (−m/p_m)=−1.

The two characters for −2 and −3 are independent; their span has squareclasses 1,−2,−3,6. The negative class −m lies in this span exactly for m=2s² or 3s². In all other cases its restriction to the common kernel is nontrivial. A reduced residue class with the indicated signs therefore exists, and Dirichlet supplies infinitely many primes in it. Each p_m is 1 modulo 3 and is 1 or 19 modulo 24.

Set P=∏p_m. Choose q>B and larger than all p_m with q≡19 modulo 24. Thus (−2/q)=+1 but (2/q)=(3/q)=−1. Choose a prime ell, distinct from the earlier primes, in the reduced simultaneous residue classes

    ell≡1 (mod 3),  P ell≡1 (mod 16),
    P ell≡q−1 (mod q²).

CRT and Dirichlet give infinitely many such ell. Put a=P ell and take ell large enough. All primes dividing a are 1 modulo 3. Also ell modulo 8 is the inverse of P modulo 8; since each factor of P is 1 or 3 modulo 8, this makes (−2/ell)=+1. Each p_m occurs exactly once in a, and q occurs exactly once in a+1. The nonexceptional m use (i); for m=2s² or 3s², q>B ensures q∤s and (m/q)=−1, so (ii) applies. Hence ALL frozen arithmetic conditions hold at the original B, with no change of theorem or requested scope.

At every odd p|a and at q|a+1, the equation with n=2 has a nonzero negative-square root and lifts by Hensel. At 3, a≡1 and a+1≡2 give the solution (1,1) modulo 3 and a nonzero derivative. At 2 the explicit basis in §2 gives the local norm-4 vector since a≡1 modulo 16.

What this DOES NOT prove: unselected prime divisors of a+1 have not been controlled. Such a divisor p can have (−2/p)=−1 and obstruct norm 4, no matter whether its valuation is odd or even. This construction therefore proves neither an all-prime local solution nor an actual norm-4 companion. It is not an asymptotic counterexample to E(B,a). It shows precisely why combining the corrected sign with the named witnesses, the 3-adic repair, and elementary character/CRT operations does not finish the desired large-B exclusion.

For a positive a≡1 modulo 16, there is an exact criterion for the particular companion used above:

    N_a and <4>⊥<−a(a+1)> are locally isometric everywhere
    iff every odd p|a(a+1) has (−2/p)=+1.

Necessity follows from representing half-norm 2 modulo each such p; sufficiency is the unit-line argument at odd primes and the explicit 2-adic basis in §2. Thus extending the fixed-B Pell example to unbounded B requires control of the ENTIRE odd-prime support of a+1, in addition to all the frozen witnesses. The CRT construction just given does not supply that control. Conversely, a proof that this support must eventually contain an obstructing prime for all frozen-allowed a would need a new argument; no such theorem is inferred here.
