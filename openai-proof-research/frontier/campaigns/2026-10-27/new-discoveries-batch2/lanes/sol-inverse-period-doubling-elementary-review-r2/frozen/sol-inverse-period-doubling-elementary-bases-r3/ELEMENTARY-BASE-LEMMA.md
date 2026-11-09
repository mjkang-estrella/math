# Eventual powers force dependence (independent ordinary proof)

Lemma. Fix integers k>=2 and M>=0. If the set {4^m:m>=M} has a regular language of canonical base-k representations, then k^r=4^s for some positive integers r,s. The same conclusion holds if a recognizable set differs from these powers by finitely many integers: remove the finite exceptions and all powers below a sufficiently large bound first, using regular finite-set Boolean closure.

Proof. Let a DFA for the exact canonical language have Q states. Choose a member w of length at least Q+1; this is possible because the set is unbounded. Among the Q+1 states after the first 1,...,Q+1 digits, two are equal. Thus w=xyz, where x is NONEMPTY, y is nonempty, and the state after x equals that after xy. The words xy^j z are accepted for all integers j>=0. Every such word begins with the same nonzero first digit of x, so it is canonical even when j=0; no leading-zero convention is being smuggled into pumping. Its length is nonzero. There is no requirement that z be nonempty.

Put r=|y|>0, h=|z|>=0, X=[x]_k>0, Y=[y]_k>=0, Z=[z]_k>=0. By positional evaluation,

    N_j=[xy^j z]_k
       = X k^(rj+h) + Y k^h (k^(rj)-1)/(k^r-1) + Z
       = A k^(rj) + B,
    A=k^h (X+Y/(k^r-1))>0,
    B=Z-k^h Y/(k^r-1).

The formula holds also at j=0 and when y consists entirely of zeroes. In particular N_j is strictly increasing and unbounded. Since all words are accepted, N_j=4^(m_j) with m_j>=M, and m_(j+1)>m_j. Thus N_(j+1)/N_j=4^(s_j) with s_j a positive integer. The displayed affine-exponential formula gives convergence of these ratios to k^r. A convergent sequence in {4,16,64,...} is eventually constant: it is eventually bounded, hence lies in a finite set, and a sufficiently small neighborhood of its limit contains at most one point of that set. Consequently its limit is 4^s for a positive integer s and k^r=4^s. This proof also rules out k^r<4 directly. No irrational-logarithm, S-unit, Cobham or substitution theorem is used.

Finally k^r=2^(2s) forces k=2^h with integer h>=1 by prime factorization: any prime dividing k divides 2. This is the only arithmetic dependence conclusion needed below. QED.
