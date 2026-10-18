# T025O54: uniformly short Egyptian fractions with distinct odd denominators

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Full author proof claim; independent proof and contribution assessment pending.** No campaign acceptance or new-to-literature assertion is made. The exact frozen target is unchanged, SHA256 f6da553993dc03592a52711922035d412ca21b6840194fb4b3440e8e7415e0b6.

## Theorem

Assume the stipulated source025 lemmas at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. There are absolute constants B>0 and b0 such that, for every odd integer b>=b0 and every integer 1<=a<b, a/b is a sum of at most B log log b distinct positive unit fractions with odd denominators. No upper bound on denominator size is asserted.

The proof uses the common dense set with two denominator valuations proved in constrained-descent.md. That lemma preserves every numerator in the stated common set, with an exceptional proportion smaller than every fixed power of S. Its modified Fourier-modulus range and terminal construction are proved there, not taken as unstated source conclusions.

## 1. An odd distinct prefix with controlled numerator

Start with x=a/b. Consider the consecutive odd denominators3,5,7,..., subtracting their reciprocals as long as each is at most the current remainder, and stop upon the first refusal or upon reaching zero. Only an absolute number of subtractions can occur: a fixed initial segment of the odd harmonic series already has sum greater than1. If a positive remainder r remains, it is less than the reciprocal of the next odd denominator d, hence less than1/3 and smaller than every prefix reciprocal.

Now apply odd greedy steps: n is the least odd integer >=1/r. The first such n exceeds the refused d, and subsequent denominators are strictly increasing. Indeed n>=5 and

    0<=r-1/n<2/[n(n-2)]<1/n.

The next denominator must exceed n. More quantitatively n<1/r+2 gives r'<=2r^2/(1+2r), so y=2r obeys y'<=y^2 and initially y<2/3. After j positive steps y_j<=(2/3)^(2^j).

Keep all fractions unreduced: r=A/C, and a step replaces (A,C) by (nA-C,nC). Thus 0<=A'<2A and C'<=C(C+2). The bounded initial prefix multiplies the starting numerator and denominator by at most absolute constants.

Put T=b^(2DC), with DC from constrained-descent.md. Stop at zero or at the first positive state C>=T. If there have been j positive odd-greedy steps without crossing, r>=1/C>1/T, whereas the preceding squaring estimate gives a contradiction once j=O(log log T). Thus the number of steps is O(log log b). At the crossing,

    T<=C<T^2+2T,
    1<=A<=b*(log b)^O(1).

C is odd, since b and all selected multipliers are odd. Define

    S=log C/(1.5DC).

Then S lies between (4/3)log b and (8/3)log b+o(1); in particular A<exp(S) for large b, uniformly in a. Also C=exp(1.5DC S) lies in the interior range required by the constrained-descent lemma. The remainder A/C is strictly less than every prefix reciprocal. If any earlier stage reached zero, its distinct odd prefix already proves the theorem.

## 2. Combining two dense expansions without collisions

Apply constrained-descent.md to S,C, obtaining ell,M0,G and X=exp(DX S). Set

    R=X/(ell A M0).

Since A<exp(S), M0<exp(DM S), and DX=DM+2, R>exp(S)/ell tends to infinity uniformly. Choose g to be the largest positive odd integer <=R. For large S, g>=R/2. Hence the integer n=g A M0 satisfies

    X/(2ell)<=n<=X/ell.

Among the n-1 splits n=u+v with u,v positive, at most epsilon(S)X have u outside G, and at most epsilon(S)X have ell v outside G. The latter bound simply injects the bad v into the complement of G by v↦ell v; it does not assume that G is equidistributed in a progression. Both tested arguments lie in[1,X]. Since epsilon(S)=o(S^-A) for every fixed A and ell<=2S^2, for large S

    2epsilon(S)X<n-1.

Choose a split with u∈G and ell v∈G.

Use the nu=0 expansion for u/(M0C), and the nu=1 expansion for

    (ell v)/(ell M0 C)=v/(M0C).

Each list is internally distinct and odd. Their denominator ell-adic valuations are respectively0 and1, so their union is distinct. Their sum is n/(M0C)=gA/C. Multiply every denominator by the odd integer g. This gives a distinct odd expansion of A/C, with O(log S) terms. The two valuation classes are now v_ell(g) and v_ell(g)+1, still disjoint; no coprimality of g and ell is required.

Finally append the prefix. Every new reciprocal is at most the total remainder A/C, which is strictly below each prefix reciprocal. Thus every new denominator exceeds every prefix denominator. All denominators are odd positive integers, and their total is less than1, so none equals1. They are therefore at least3. The total length is O(log log b)+O(log S)=O(log log b), with absolute constants and onset uniform in a. This proves the complete frozen theorem.

## 3. Dependency boundary

The source supplies the uniform shifted truncated-divisor moment for any fixed moment order, the reciprocal-phase estimate with fixed exponent range, the prime-product architecture, and its original recurrence argument. The new construction imposes a multiplier congruence modulo the growing prime2ell, replaces the binary terminal stage by valuation-separated base5 digits, retains a common good-numerator set for M0 and ell M0, and uses its small exceptional density on a sparse dilation to merge two expansions in disjoint valuation classes. The final proof never invokes unrestricted duplicate removal.

Classical PNT is used only to obtain the source prime supply and an ell avoiding C. No quantitative PNT error is needed. Erdős–Turán, orthogonality, Cauchy–Schwarz, Markov, Hölder, and the source recurrence are credited rather than claimed new. The claim of a new operational contribution is the compatible constrained construction and collision-free merge, not those estimates individually. Independent contribution assessment remains necessary.
