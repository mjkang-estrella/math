# Four-column arithmetic route

Full T191V56 remains unresolved. Every assertion below that is only a desired estimate is explicitly marked. Source191's three-column theorems are stipulated; they do not state their four-column analogues.

## 1. The norm obstruction does extend

Fix an odd positive extension degree d, and an odd prime r. Over F_(r^d), use z(xi)=(1,xi,xi^2,xi^3). The determinant of four such columns is the Vandermonde product and is nonzero for four distinct labels. Its norm to F_r is alternating because d is odd, and is homogeneous of degree d in each of four groups of 4d coordinates. Expanding in the M=binomial(5d-1,d) degree-d monomials expresses it as a sum of T=binomial(M,4) determinants of four monomial rows, with a scalar in the first row. Repeated monomial indices vanish by alternation in odd characteristic; this uses no division by 4!.

Set k=T^3+1. For 0<=a<T designate positions

    a, Ta, T^2 a, T^3-(T^2+T+1)a

in the four rows respectively. Each lies in [0,k-1], with no repetition within a row. A sum of four designated positions equals k-1 precisely when their four labels a agree: reduce the equality modulo T, subtract, divide by T, and repeat. Thus precisely the desired four-row determinants contribute to the coefficient at k-1.

Choose L divisible by r. Let B be prime with 400 k^3 L^4 < B <= 800 k^3 L^4, and h=B^k. Prescribe the monomial residues at designated digits and zero elsewhere, and draw digits independently from 1,...,L in their prescribed classes modulo r. Each class has L/r choices; every entry is a unit modulo B. For the determinant polynomial F(Y), every coefficient has absolute value at most A=24 k^3 L^4: fix a permutation and three digit positions to determine the fourth. The coefficient at k-1 is nonzero modulo r when all four labels differ.

The truncated integer representative S=sum_(u<k) gamma_u B^u then satisfies |S| <= A(h-1)/(B-1)<h/2. Its top nonzero coefficient gives |S|> B^(k-1)/2, since the lower coefficients contribute at most A(B^(k-1)-1)/(B-1)<.061 B^(k-1). Thus no representative of det C modulo h has absolute value at most tau=floor(B^(k-1)/2). SL4 mixing preserves this. A small determinant requires a repeated label, with probability at most 6r^(-d).

This is a fully checked algebraic adaptation of source191 section 03, not a substantial theorem by itself. The fixed positional coding and carry estimates are credited to that source; optimizing T or k would not establish the full target.

## 2. What the four-dimensional orbit really costs

For any 4x4 matrix C over Z/h with a unit entry, elementary Smith elimination gives diagonal form (1,D,E,F), where D=B^b,E=B^e,F=B^f and 0<=b<=e<=f<=k. Its row lattice has index I=DEF. A GL4 stabilizer has at most D^4 E^4 F^4 elements: the first column is fixed, and each subsequent column differs from the corresponding standard column by entries annihilated by D,E,F. Its determinant image has at least (1-B^(-1))F elements, by changing only the last diagonal unit congruent to 1 modulo h/F. The GL4 group size is h^16 product_(i=1)^4(1-B^(-i)). Orbit-stabilizer and the determinant map therefore give

    |SL4(Z/h) C| >= c h^15/(D^4 E^4 F^3),

with absolute c>0, including singular residue matrices.

For a four-column auxiliary distribution with normalized weight W, exact CRT lifting would have the factor h^16/(N^16 |orbit|). If one could prove the REQUIRED weighted fixed-determinant bound

    sum_(A: det A=t, orbit condition) W(A)
       <= (log(2N))^O(1) N^12 / (DEF)^3,             (FD4)

uniformly for |t|<=tau, then the conditional bad-quadruple probability would be at most

    (log(2N))^O(1) h D E / N^4.

This follows by exact cancellation of D,E,F powers. FD4 is NOT supplied by the three-column source and is NOT proved here, even for nonzero t. In particular the argument already requires a new uniform conditional moment of DE, not the source's moment of D alone.

## 3. The source digit conditioning does not close that moment

First take the favorable stratum D=1 and specify a unit 2x2 pivot, relabelled to the top left. Condition on the complete first two rows and the first two entries of the last two rows. The remaining four entries are independent. Vanishing of all 3x3 minors modulo B^j forces those four entries to equal their Schur-complement values modulo B^j. Each equality fixes its first j base-B digits, and has probability at most (r/L)^j. For this pivot, therefore,

    Pr(E>=B^j AND this pivot is a unit | fixed labels)
         <= (r/L)^(4j).

A finite union over pivots only changes a constant. The event that the pivot is a unit depends only on conditioned entries, so there is no unjustified independence after conditioning on it. This estimate handles only D=1; D>1 needs additional work.

Tail summation bounds the corresponding E moment by a constant times

    1 + sum_(j=1)^k [B(r/L)^4]^j.

But B(r/L)^4 > 400 k^3 r^4. The source's analogous three-column ratio contracts because its carry scale is L^3 and the codimension-four constraint wins. Here that argument yields no bounded moment, whatever fixed L=r^A is chosen. This is a failure of this upper-bound argument, NOT a lower bound on the actual moment and NOT a counterexample to T191V56.

The loss is consequential: h/tau is of order B. At the intended alteration size n~r (N^4/tau)^(1/3), the normalized expected number of bad quadruples, even under FD4, has size bounded by roughly r^3(h/tau) E[DE 1_collision]. A bound uniform in labels and in r, or a suitably controlled power independent of k, is needed; merely declaring the source constant dimension-dependent does not control a growing r.

## 4. A genuinely different refinement: carry-free minor jets

Every 3x3 minor of the digit-polynomial matrix C(Y) has coefficients bounded by 6k^2 L^3, which is less than B. If its evaluation at B is divisible by B^j, then its constant coefficient, being a multiple of B of absolute value <B, is zero. Divide by B and repeat. Therefore divisibility by B^j is equivalent to exact vanishing of its first j polynomial coefficients.

Consequently on D=1, E>=B^j implies rank at most two over Q[Y]/(Y^j), with a pivot whose constant determinant is nonzero. This is more structured than four unrelated finite-field congruences. It suggests counting bounded INTEGER polynomial matrices of rank two to order j, keeping their prescribed residue classes modulo r.

I attempted the Schur recursion in this ring. With the first two rows and the first two coordinates of the last rows prescribed, inversion of the pivot matrix determines every remaining coefficient recursively. This establishes at most one admissible value at each of the four remaining positions per level, exactly recovering the (r/L)^(4j) bound. It does not by itself estimate how often the rationally determined value is integral, in the required residue class, and inside [1,L]. A new estimate for those simultaneous integrality and size constraints is needed. Treating their occurrence as four extra independent random events is unjustified: the rational functions share the pivot determinant and earlier coefficients.

One sufficient but UNPROVED improvement on this stratum would be a uniform bound C^j(r/L)^(5j), for C depending only on fixed construction data. With L=r^A, A>5, the new ratio B(r/L)^5=O_k(r^(5-A)) contracts. This is stated solely to quantify the missing strength, not to assert this particular exponent is true. The nonunit-pivot strata and FD4 would still remain.

The formal-polynomial reformulation is an actual additional attempt, not a proof. No dimension count for a real algebraic variety is converted to the required integer count. No unrestricted uniform finite-field law is substituted for the short residue-restricted digit distribution.
