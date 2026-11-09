# Independent preliminary review: Guo 1901.07908v1, Conjecture 6.1

**Recommendation: mathematical PASS; substantive-credit EXCLUDE as a complete routine classical/source-method adaptation. Stop further investment. Literature-priority clearance remains HOLD.** This is a review recommendation to root, not acceptance, a count change, or a claim that an exact later published proof has been located. Counts remain 9 additional / 39 total / next 40.

## Source and exact scope

I read the frozen actual nine-page Guo body, particularly Sections 2, 4–6. Its p8 Conjecture 6.1 is exactly the sum in the assignment: every positive integer n congruent to 4 or 7 modulo 9, with j=0 through n−1 and modulus Phi_n(q)^2. Composite n are included. Its Section 6 introduction explicitly identifies the asymmetry and difficulty of finding a corresponding parameter generalization. Theorem 1.1 is **not** a literal subsumer: it has repeated identical top parameters, d of them, and different residue hypotheses. Theorem 5.1 likewise has repeated top parameters (q²,q²,q⁵) in the same residue classes; this does not equal (q,q²,q⁶).

The actual Schilling–Warnaar math/9909044v1 p1 Eq(1.1) states the terminating q-Pfaff–Saalschütz formula. In unambiguous renamed notation it is

    sum_{j=0}^L (b,c,Q^(-L);Q)_j Q^j /
       [(Q;Q)_j (C;Q)_j (bc Q^(1-L)/C;Q)_j]
      = (C/b,C/c;Q)_L / (C,C/(bc);Q)_L.

Set C=Q and bc=Q^(L+1). The two explicit lower parameters become Q and Q; the implicit factorial supplies the third. The right denominator becomes (Q,Q^(-L);Q)_L. Thus the candidate's balanced formula is exactly correct. All L used here are positive, so even the source's convention for Z+ at L=0 is irrelevant. The formula is a finite rational identity; no analytic convergence or numerical continuation premise is required. I read Eq(1.1) and its introductory context, not the full proof of Schilling–Warnaar's subsequent generalized theorem.

## Independent complete bridge and boundary audit

Write Q=q^9, delta=q^n−1 and work over R=Q[q,q^(-1)] localized at the prime polynomial Phi_n. Define

    f(A)=sum_{j=0}^{n-1}(Aq,q²/A,q⁶;Q)_j Q^j/(Q;Q)_j³.

The coefficients lie in R and f is Laurent polynomial in A. Since gcd(n,9)=1, no exponent 9i, 1<=i<n, is divisible by n; consequently every displayed original denominator is a unit. The following table is obtained by solving the terminating exponents modulo 9, and the numerator zero indices modulo n. All entries are affine in the integer l>=0.

| n | t1 | t2 | L1 | L2 | J3 | J7 | J8 |
|---|---|---|---|---|---|---|---|---|
|9l+4|7|5|7l+3|5l+2|3l+1|4l+1|2l|
|9l+7|4|8|4l+3|8l+6|3l+2|l|5l+3|

Here 9L1=t1 n−1, 9L2=t2 n−2. Both L are positive and less than n. At A=q^(−t1 n), the top Aq equals Q^(−L1); at A=q^(t2 n), the top q²/A equals Q^(−L2). Every term after the indicated L vanishes exactly because its top product includes 1−Q^0. The surviving other top products have product Q^(L+1): their exponents sum to 8+t1 n=9(L1+1), respectively 7+t2 n=9(L2+1). Thus the exact classical evaluations are

    f(q^(-t1 n))=(q^(7-t1 n),q³;Q)_L1 /
                       [(Q;Q)_L1 (Q^(-L1);Q)_L1],
    f(q^( t2 n))=(q^(8-t2 n),q³;Q)_L2 /
                       [(Q;Q)_L2 (Q^(-L2);Q)_L2].

All denominator exponents belong to {9,...,9L} or {−9L,...,−9}, so they are nonzero and Phi_n units. The first numerator's zero indices are J7 and J3, the second's J8 and J3. In fact the factors at those indices are precisely **1−q^(−3n)** and **1−q^(3n)** in both evaluations. This supplies two cyclotomic factors independently of whether indices coincide.

The four required strict differences (L1−J3,L1−J7,L2−J3,L2−J8) are (4l+2,3l+2,2l+1,3l+2) for n=9l+4 and (l+1,3l+3,5l+4,3l+3) for n=9l+7. Also n−L1,n−L2 are (2l+1,4l+2) or (5l+4,l+1). Hence all index inequalities hold uniformly, including l=0. For n=4 the tuple (L1,L2,J3,J7,J8) is (3,2,1,1,0); for n=7 it is (3,6,2,0,3). There is no discarded boundary term and no primality step.

Both exact evaluations are therefore zero modulo Phi_n². For any integer c, Laurent polynomial expansion at the unit A=1 gives

    f(q^(cn)) = f(1)+c delta f'(1) mod Phi_n².

This follows algebraically from q^(cn)=(1+delta)^c=1+c delta modulo delta², including c<0; the remainder is divisible by (A−1)² after clearing an A monomial. Since t1+t2=12, an especially transparent final interpolation is

    f(1) = [t2 f(q^(-t1 n))+t1 f(q^(t2 n))]/12 mod Phi_n².

The derivative terms cancel exactly. Twelve is invertible in the rational coefficient ring. This establishes the entire source assertion, conditional only on the source-verified classical identity. No finite experiment supplies a universal inference.

## Meaning over integers

The sum is a rational function, generally not an integer polynomial. The valid interpretation is divisibility after clearing a denominator coprime to Phi_n. This is not a claim of coefficientwise congruence of arbitrary rational numbers modulo an integer. Let D=(Q;Q)_(n−1)^3 in Z[q]. Then N=D f(1) is an integer polynomial and gcd(D,Phi_n)=1 over Q[q]. The proof gives Phi_n² | N in Q[q]. Since Phi_n² is monic in Z[q], polynomial division gives the quotient in Z[q] as well. Thus inversion of 12 creates no integrality gap in this denominator-cleared interpretation. One need not assert that 12 is a unit in a localization of Z[q] which has not inverted it. Negative powers in intermediate evaluations are units and cause no loss when returning to N. This also handles composite n divisible by 2 or other small primes.

## Classical/source adaptation adjudication

The objection is supported by an applicable bridge, not the number of proof lines. Guo's actual p3 discussion and Theorem 2.1 insert a parameter, specialize it to terminating q-powers, evaluate finite sums, check cyclotomic denominator units, and coalesce the parameter to obtain a square modulus. Section 4 implements this for a three-top-factor series, and Theorem 5.1 implements the base q^9 setting. Guo's terminating evaluation uses a finite q-binomial polynomial-degree identity; the reviewed argument substitutes exactly the classical balanced 3phi2 evaluation above and elementary two-node first-order interpolation. The asymmetric exponents require unequal nodes −t1 and t2; solving their two residue equations and the displayed affine inequalities completes the bridge. There is no remaining scientific lemma or conjectural matching condition.

This does **not** show Guo already wrote this exact proof, nor that one of his named theorems specializes literally to it. It does show a full routine application of a classical summation and the source's own deformation strategy, with only explicit residue arithmetic and linear Taylor interpolation left. Under the campaign rule excluding routine classical/source adaptations, I recommend no substantive discovery credit and no formalization/manuscript investment. A different substantive result would require a genuinely different target; elaborating this proof does not resolve that credit objection.

Closest bodies additionally compared: Guo–Schlosser 1901.07962v3 introductory Theorems 1–4 and the Section 2 proof mechanism use creative microscoping and terminal evaluations, but do not literally state this asymmetric base-9 sum. Guo–Zudilin 1803.01830, the introductory deformation discussion and the actual Theorem 4.8 proof around pp16–17, explicitly use a terminating q-Saalschütz evaluation in a parameter/cyclotomic argument. These establish prior method availability, not an exact prior resolution of Conjecture 6.1. No claim of full reading of these two longer neighboring bodies is made.

## Public-proof and chronology limit

Schilling–Warnaar's body is dated 8 September 1999. Guo's frozen abstract history records v1 at 22 January 2019 03:40:32 UTC; Guo–Schlosser's compared body is v3, 19 February 2019. These precede this review. The current arXiv searches on 30 October 2026 (receipts in search-provenance.json) independently return just the original Guo item for its exact title and no results for the exact Guo/Conjecture 6.1 query. These are metadata searches, not full-text citation indexes: they cannot rule out a later exact proof. No later exact public proof was established from the compared cached bodies. Current registry heads and inaccessible historical intervals remain parked; no forbidden API/raw/codeload/diff/patch or challenge route was retried. Literature-priority status is **bounded HOLD**, even though the independent routine-credit exclusion is actionable.

## Ancillary Sun exclusion

I read Sun1101.1946v4 p27 Conjecture 4.4, Mao–Pan1801.02213v2 pp1–2 Theorem 1.1 and its proof pp3–7. In the local cache, `divisibility.txt` is this Mao–Pan paper; `maopan.txt` is a different Mao–Pan paper (p-adic analogues of hypergeometric identities), so filenames alone are not source attribution. Set Mao–Pan's r=n, alpha=−x, a=k. For n>=2,

    k <= (p+1)/(2n+1) < (p+n)/(2n+1).

The sign identity binom(x,j)=(−1)^j(−x)_j/j!, with odd power 2n+1, converts Sun's literal alternating sum to their all-alpha hypergeometric sum. Every j! for j<p is a p-unit. All p-adic x and all admissible k remain covered, with empty ranges vacuous. The actual proof treats p | (2r+1) separately, so that case is not excluded. It uses Karlsson–Minton termination, Taylor expansion and harmonic reflection. The printed global derivative equality is only needed at zero, where symmetry validates it; the later p−2k cutoff typos are read as p−2a consistently with the derivation. Thus Sun4.4 is already publicly resolved by the surviving v2 theorem (5 March 2018), and deserves no credit here. No new Sun investigation was undertaken.

## Verification and gate separation

`check.py` is independently written; no candidate checker is reused. It computes common-denominator integer numerators directly modulo monic Phi_n² for n=4,7,13,16,22,25,31,34,40,49, for the target and both deformations. It checks denominator coprimality and both exact rational identities at q=2, and verifies the twelve uniform affine positivity conditions by coefficient signs. All pass. The finite checks are corroboration only; the preceding argument is the universal proof.

Source fidelity PASS; mathematical derivation PASS; substantive credit EXCLUDE (recommendation); literature priority HOLD; formal feasibility plausible but **UNVERIFIED**, with no Lean endpoint or residual-bridge audit attempted. All arithmetic, retrieval, file-copy and hash helpers use the specified 512MiB/210CPU/230wall guard and required environment; native bounded reads and apply_patch were used as permitted. The initial inventory shell command was outside the guard and overbroad; this protocol failure is retained in failures.md. Final source original/copy rechecks and the manifest check are separate guarded verification after final writes. Root alone decides acceptance; this review changes no shared state.
