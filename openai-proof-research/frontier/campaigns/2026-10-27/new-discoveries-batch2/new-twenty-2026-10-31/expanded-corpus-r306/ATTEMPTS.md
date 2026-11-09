# Ordinary proof attempts

No mathematical enumeration, solver, numerical search, Lean process or child was run.

## 376322 — sustained full route

See CANDIDATE.md for the entire ordinary proof, rejected unshifted/quotient-only shortcuts, exact semantic bridges, source comparison and dormant plan. This is the strongest route. It remains held on independent proof review, compound-graph subsumption, current-registry coverage and formalization. Credit 0.

## 366639 — complete classical reduction, credit 0

Let T_S be the first ending time of a nonempty word S of length r in iid fair bits. For every m, T_S>m iff the first m bits avoid S. Reversal is a bijection of the 2^m equiprobable words of length m and maps avoidance of S exactly to avoidance of rev(S): a contiguous occurrence reverses to a contiguous occurrence at the reflected location, and applying reversal again gives the converse. Hence P(T_S>m)=P(T_rev(S)>m) for every m, including m<r. Thus the entire first-occurrence distributions agree. Summing tail probabilities proves equality of expectations. They are finite: independent disjoint r-block trials succeed with probability 2^-r, so P(T_S>qr)<=(1-2^-r)^q and E T_S<=r 2^r. The empty word, if allowed, has ending time 0 for both orders.

An initial route through the classical border formula E T_S=sum_{j:prefix_j(S)=suffix_j(S)}2^j also closes because reversal preserves borders. It needs an unnecessary waiting-time lemma; the avoidance bijection gives the full scope directly and is the complete classical time-reversal bridge. The source's intuitive average-interarrival explanation conflates interarrival time and first waiting time and is not used. Search additionally found a 2023 primary article reporting reversal equality of whole waiting-time distributions (ScienceDirect S0167715223000329); its full proof was not read here. The explicit avoidance proof already establishes the exclusion, without relying on that abstract or treating a short proof itself as disqualifying.

Primary Conjecture 4.2 and introductory first-occurrence definition were read; v1 and v2 bodies downloaded. No novelty investment or Pi task is warranted.

## 367492 — sustained exact removal route, still missing stability

Write m=|A|, n=|B|, S=A+B, C=A+_R B, and T=S minus C. Every representation of a removed sum t must be forbidden. Since exactly one pair is forbidden in each column b, the B-supports of the representation fibers of distinct t in T are disjoint, and sum_{t in T}r(t)<=n. Conversely, if a set T of sums has at most one representation in each column, all of T can be removed by choosing those forbidden partners and filling unused R values arbitrarily. Thus a refutation requires a genuinely in-scope finite A,B and at least |S|-(m+n-4) sums with disjoint representation supports. This is exact, not a matching assumption: R need not be injective.

The first shortcut, subtract n deletions from Cauchy–Davenport, gives only m-1 and does not close the requested m+n-3. A second attempt uses Pollard-style truncated representation bounds: a lower bound sum_s min(r(s),t)>=t(m+n-t), combined with the removal budget and |C|<=m+n-4, gives n>=t(4-t). At t=2 this only forces n>=4, and at t=3 only n>=3. Thus it does not exclude general n. This is a conditional use of a classical bound as an obstruction diagnostic, not a newly proved ingredient or a completed proof.

In a rectified interval case A={0,...,m-1}, B={0,...,n-1}, m>=n>=2, at most two sums can be removed. Any three removed sums t1<t2<t3 force two column supports to overlap, as follows. The endpoint supports for sums 0,...,n-2 are nested prefixes; supports for m,...,m+n-2 are nested suffixes; every central sum has full B-support. At most one removed sum comes from either tail and none can coexist with a central sum. Therefore |C|>=m+n-3. This establishes an interval special case only. For n=1, |C|=m-1>=m-2, and n=2,3 the preceding representation-bound diagnostic would suffice if its full hypotheses are imported, but no partial-conjunct credit is claimed.

The obstacle is a uniform finite-field stability/rectification lemma that controls removable representation fibers at density m+2n<=p. One cannot use ordinary integer ordering across modular wraparound. Interpolating R by a degree n-1 polynomial and multiplying a sumset-vanishing polynomial introduces too much degree for the sharp two-unit loss; noninjectivity prevents replacing R by a linear forbidden-diagonal factor. Source Conjecture 1.13, surrounding Theorem 1.11 counterexample regime, and function/relation definitions were read. The public dense matching counterexample has 2|A| near 12p/11 and is outside m+2n<=p when A=B; it cannot be recycled here. v1/v2/v3 were obtained; the current journal DOI returned403, with no retry. No finite witness, full proof or Pi plan survives.

## 366579 — literal correction excluded, substantive route parked

Under the printed label range {0,...,diam G}, K_3 with D={0} has distinct singleton neighborhoods but no labeling bijection because 3!=2. This is solely the source/record label-range defect and receives0. Under the intended {1,...,|V|} range it vanishes: every D={0} labeling works. Necessity of distinct neighborhoods is immediate by equal sums. For sufficiency, arbitrary distinct neighborhood incidence rows do not guarantee that some permutation separates all row sums: a union of equality hyperplanes might cover all permutations. Exponentially separated labels would work but are not an allowed permutation. No genuine intended-domain certificate was found; do not send the K_3 correction to Pi.


## 367383 — complete classical CRT bridge, credit0

For positive n>=2, adjacent distinct residues x,y mean x+y is a unit. For odd n, choose z modulo each prime divisor p to avoid -x and -y. Since p>=3 a residue is available; CRT lifts these residues to Z_n. Then x+z and y+z are units. If x,y were not already adjacent, z cannot equal either endpoint: z=x would imply x+y unit, and similarly z=y. This gives a length-two path. For even n, residues of the same parity have a common neighbor: modulo2 choose opposite parity, and modulo odd prime divisors avoid -x and -y as before. Opposite-parity x,y first take t=1-x, so x+t=1 is a unit and t!=x by parity. Then t,y have the same parity and are equal, adjacent, or joined by the established two-step construction, giving an x,y walk of length at most3; shortening it yields a path. For n=1 the usual singleton graph convention is connected of diameter0. No claim is made about the non-finite ring Z_0. This completely reduces the positive finite-modulus scope to classical CRT, independently of the partially read source proof. The reduction, not mere ease or familiarity, is the reason for zero credit.
