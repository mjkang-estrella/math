# Sustained routes and exact limitations

No candidate has a full ordinary solution or a literal Lean endpoint. Credit is zero.

## Weakly consecutive sequences (361538)

For distinct positions i,j, the WCS condition is equivalent to gcd(v_i,|i-j|)=gcd(v_j,|i-j|): the positive divisors of these gcds must coincide. This gives the complete-domain CSP in the scripts. A second necessary constraint comes from cardinality: for d<=k with floor(k/d)>0, the positions of multiples of d form one complete residue class modulo d. Each residue has floor(k/d) or floor(k/d)+1 members; two occupied residue classes would already contain too many multiples. Thus if v is placed at zero-based position i, every divisor d of v requires i%d >= k%d. This supplies the unary filtering in the second large search, without assuming the conjectured endpoint position of 1.

For a one-transposition neighbor of a WCS, divisors d<=k/2 cannot change their occupied residue class by exchanging just one member (each class has at least two members). Hence exchanged values have identical divisors through k/2. Divisors above k/2 have one multiple, and its new position must be in the singleton-residue interval [k-d+1,d]. This is the exact neighborhood test in wcs.py. It is not an enumeration of all WCSs and does not prove uniqueness of rule histories.

The unfiltered large CSP was capped at 30000 nodes for each k=501..505 and is incomplete. Do not quote its one found solution as the total. Complete small permutations and all tested seed transpositions are separate coverage. A full proof would need a structural theorem excluding all other residue assignments, then a canonical factorization of the surviving permutations into source rules. Neither lemma is proved.

## Stack dynamics (347736)

The stack is maintained avoiding the consecutive pattern read from top to bottom. Only the new top window can violate the invariant when a letter is pushed; repeated pops are therefore exact. A complete functional graph on S_n is constructed; repeated removal of indegree-zero nodes leaves precisely all cycles. Its vertex set is compared with the literal consecutive avoidance class for sigma and reversed sigma. The source example SC_231(265413)=653142 is reproduced.

Two full sweeps were followed by length-five patterns on n=9 in batches. Counts in logs are complete only for finished pattern rows. Every pattern row records n!, periodic-node count and symmetric-difference size. No violation has been found. A universal proof still requires a monotone statistic forcing every cycle to avoid both patterns; the k=3 proof does not automatically extend.

## Blade numerator positivity (340676)

Proposition 8.3 gives T(n,k)=sum_i S(n,i)s(i-1,k-1). For diagonal j take the sequence T(n,n-j) starting at n=j+1. Multiply its ordinary series by (1-x)^(2j+1); the finite differences give numerator coefficients. The scripts retain exact integers and check trailing cancellation, symmetry, factorial sum and unimodality through j=100. The gamma transform subtracts gamma_i*x^i*(1+x)^(j-2i) in increasing i; all gamma coefficients through j=100 are nonnegative.

A nonnegative gamma expansion would prove unimodality, because each basis polynomial is symmetric and increases to the common center. This is only a conditional mechanism: no all-j combinatorial gamma interpretation or positive recurrence was proved. Appendix A already supplies symmetry and factorial sum, so neither is a new discovery.

## Pfaffian consecutive factors (382189)

Fraction-free skew elimination uses the update (a_ij*p-a_zi*a_(z+1)j+a_zj*a_(z+1)i)/previous_pivot. Every division is checked exact. The leading pivots are successive principal Pfaffians. At t=1, coefficients lie in Z[k]; divide the n-th pivot by the preceding o polynomial and check zero remainder, retaining every coefficient through n=32. Total degree n of the Pfaffian, and factor degrees floor((n-1)/2),floor(n/2), permit homogenization with a single t factor, recovering finite instances of the two-variable identity. Integer substitutions through n=48 are a separate weaker check and stop at zero pivots.

No all-n divisibility invariant has been found. A finite symbolic extension, even beyond n=25, is not a conjecture solution.

## Additional source-scope gates

357800 is exactly the source's Theorem 3.1 (also implied by Theorem 1.1); its actual proof was read. It is excluded as already proved. 382272 appears as v1 Conjecture 8.45 but the current version constructs the required representative in Theorem 8.3 and the Section 8.5 proof via Lemma 8.10 and Table 1. Older affine-coordinate constants differ; no credit for correcting them.

365977 has the positive-center disk typo in the primary source itself, together with a negative axis. The h* real-rootedness search addresses a meaningful part of the intended scope. A sign-error refutation is excluded. 372282 concerns the fourth-order Steklov problem; applying ordinary Steklov eigenvalues would refute a different statement.

338455(b) says forests in both retrieved text and MathDB. Taken literally, already empty forests and disjoint path components create a forest/tree counting ambiguity. This is a scope defect, not a qualifying new exact solution. Moment tests address the meaningful ordering claim (a); they do not settle all characteristic coefficients.
