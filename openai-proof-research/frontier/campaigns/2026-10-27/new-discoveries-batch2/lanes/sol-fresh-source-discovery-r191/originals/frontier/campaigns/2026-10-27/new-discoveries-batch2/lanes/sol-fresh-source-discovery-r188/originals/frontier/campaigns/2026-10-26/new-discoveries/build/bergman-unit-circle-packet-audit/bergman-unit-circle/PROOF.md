# Full unit-circle nonvanishing route: Edholm–Mathew Q(m,n)

Research date:2026-10-26. MathDB368572. Complete exact-source proof and78-declaration Lean certificate; see final-status section below. One combined outcome only.

Source: Luke D. Edholm and Vikram T. Mathew, *Arithmetic properties and zeros of the Bergman kernel on a class of quotient domains*, arXiv2505.20489v3 (14May2026); actual latest published version Mathematische Zeitschrift313(2026),43, published6June2026, DOI10.1007/s00209-026-04059-8, Conjecture4.20. The full open-access published body was checked and retains this exact conjecture. Actual latest source says the full conjecture remains open, including difference5; differences1,2,3,4,6 known, plus infinitely many pairs at each difference. Source says a related paper is in preparation. Must check nearest source and any subsequent publication before final acceptance.

## Literal source coefficients

Write m>n≥1, gcd(m,n)=1, k=m−n, and S_m(w)=Σ_{r=0}^{m−1}w^r. The source's triangular integers D_m(r) are exactly the coefficients of S_m(w)^2, zero outside0≤r≤2m−2. Proposition1.10/equation1.11 gives

P(s,t)=Σ_{r,q=0}^{2m−2; q−nr≡n−1 (modm)} D_m(r)D_m(q) s^r t^((q−nr−m−n+1+2mn)/m).

The displayed quotient is an integer by the constraint; its value lies in0..2n. The source defines Q(z)=z^(1−2n)P(z,z). Thus the above is exactly the source polynomial, not a proxy.

## Roots-of-unity sum of squares

Let ω be a primitive mth root of unity. For unit complex a,b set s=a b^n,t=b^m. The weighted roots-of-unity sum itself is already present in Almughrabi2023, equation24, and receives full prior credit. Its exact source coefficient normalization gives

b^(m+n−1−2mn) P(s,t)
= (1/m)Σ_{j=0}^{m−1} ω^((1−n)j) S_m(aω^(−nj))^2 S_m(bω^j)^2.

Indeed the coefficient at a^r b^q is selected precisely when q−nr+1−n≡0(modm). On the unit circle S_m(u)^2=u^(m−1)|S_m(u)|². The phase in each summand is ω^((1−n)jm)=1, so

P(s,t)/(s^(m−1)t^n)
= (1/m)Σ_j |S_m(aω^(−nj))|² |S_m(bω^j)|².                 (SOS)

For |z|=1 choose any unit b with b^m=z, and a=z b^(−n), giving s=t=z. Then the left side equals z^(−k)Q(z).

Strict positivity:
- If z≠1 then every S_m(bω^j) is nonzero, because (bω^j)^m=z≠1. If a^m≠1 then all first factors are nonzero. If a^m=1, coprimality makes ω^(−nj) run through all mth roots, so some aω^(−nj)=1 and its geometric sum is m≠0. Thus at least one summand is positive.
- If z=1 choose j with bω^j=1. Then aω^(−nj)=a b^n=z=1; the same summand is m^4>0.

Thus z^(−k)Q(z) is a strictly positive real number for every unit z. In particular Q has no unit-circle root, proving the full source conjecture's nonvanishing assertion. Root allocation then follows from the known source palindromicity and its nonzero constant coefficient; any claim of the root allocation in Lean also needs that source bridge.

## Alternative finite polynomial SOS (avoids analytic limits)

Define for0≤r<m

A_r(z)=Σ_{p=0}^{m−1} z^(p−floor((np+r)/m)).

All exponents are nonnegative since np+r≤(m−1)p+m−1<m(p+1), and they are at most k. Parseval on the cyclic group, applied to S_m(aω^(−nj))S_m(bω^j), transforms (SOS) into

z^(−k)Q(z)=Σ_{r=0}^{m−1}|A_r(z)|²  (|z|=1).              (finite SOS)

To see the grouped terms: for each p and residue r, the unique q∈0..m−1 with q−np≡r is q=np+r−m floor((np+r)/m); then a^p b^q=b^r z^(p−floor((np+r)/m)).

Only A_0,A_1 are needed for strictness. Since gcd(m,n)=1, exactly one p∈1..m−1 satisfies np≡m−1(modm). Writing np=mq+m−1, one gets

A_1(z)−A_0(z)=z^(p−q−1)(1−z).

All other floor terms remain unchanged. Here p−q≥1. For z≠1 this difference is nonzero, so the two polynomials cannot both vanish. For z=1, A_0(1)=m. Hence the SOS is strictly positive without exceptional boundary arguments.

Example m2,n1: A_0=1+z,A_1=2, so z^(−1)Q(z)=|1+z|²+4=6+z+z^(−1), matching the source table.

## Status and prior-art cautions

The full algebraic proof and source formalization now pass independent review and strict replay. The weighted roots-of-unity identity is already Almughrabi2023 Eq24 and receives no novelty claim. The source's older kernel formulas and nearest2024 monomial-domain paper were read and credited; no earlier full strict boundary conclusion was found. The source's mentioned in-preparation successor was not located or read. The contribution is the full all-coprime-pairs source conjecture, with this bounded prior-art limit, not new classical tools or a global priority guarantee.

## Exact finite validation

`bergman_exact_check.py` independently constructs the source five pieces q0,…,q4 directly from its ceiling L and κ formulas, and compares the complete integer polynomial with the finite SOS expansion. All1965coprimepairs2≤m≤80 passed; the alternative D_m formula was also checked for m≤25, as was every A1−A0 difference identity. This is experimental validation of the general proof, not a finite replacement for it. Results: `bergman-exact-check.json`.

## Direct combinatorial proof of finite SOS coefficient identity

D_m(r) counts ordered p,p′∈0..m−1 with p−p′=r−m+1. Replacing both triangular D_m factors by these difference counts turns the source congruence into q−np≡q′−np′ (modm). The source exponent becomes k+(k(p−p′)+(q−q′))/m. For a fixed residue r, write q=np+r−m floor((np+r)/m), and similarly q′. The exponent is k+e_r(p)−e_r(p′), where e_r(p)=p−floor((np+r)/m). Summing gives exactly Σ_r z^k A_r(z)A_r(z^(−1)). This derivation avoids roots of unity and identifies the actual source coefficients without assuming an unproved source-to-SOS bridge.


## Ordinary polynomial and final source root count

BergmanPolynomial defines naturalQ with coefficients D_m(r)D_m(q), selected by the exact source congruence and integer exponent E=((m−n)r+q−n+1)/m. For selected0≤r,q≤2m−2, mE equals that numerator. It is greater than−m and less than m(2(m−n)+1), proving0≤E≤2(m−n) before E.toNat is used. Evaluation after mapping natural coefficients to complex coefficients equals compressedQ at every complex argument and the literal sourceQ at every nonzero argument. Thus no proxy/source hypothesis remains.

The term r0,q=n−1 contributes positively to coefficient0. The term r=2m−2,q=2m−n−1 contributes positively to coefficient2(m−n). Nonnegative natural coefficients prevent cancellation. The exact degree is2(m−n) and the constant is nonzero. Mirror indices r→2m−2−r,q→2m−2−q preserve D and the congruence and replace E by2(m−n)−E. The finite sum therefore equals its actual polynomial reverse.

BergmanRootAllocation uses full complex factorization to prove the exact reciprocal-root multiset identity. The nonzero constant excludes zero roots, and inversion interchanges norm<1 with norm>1 preserving every multiplicity. Circle nonvanishing excludes the remaining norm1 case. The total complex root count is the degree2(m−n), so the punctured-disc filter has cardinality exactlym−n. BergmanConclusion discharges all generic premises from the actual source polynomial. Its source_full_conjecture_368572 is the conjunction of nonvanishing and this exact source count.

All ten modules and78 declarations pass pinned warning-as-error replay with only propext,Classical.choice,Quot.sound. Independent review roles, final manuscript hash and declaration receipts are included; no formal proof hole or source/SOS/degree/reciprocity/root-count assumption is left. The general Laurent identity is proved mathematically above, while Lean's SOS is specialized to unit inputs and suffices for the full certified source conclusion.
