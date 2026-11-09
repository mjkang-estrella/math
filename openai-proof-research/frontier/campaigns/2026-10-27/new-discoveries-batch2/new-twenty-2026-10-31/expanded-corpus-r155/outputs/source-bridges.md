# Source-ingredient and normalization exclusions

## 333026: finite prime-set normalization

Source: Berliner et al., Section 3.1, Definition 13 and Conjecture 14; downloaded current arXiv PDF is the Journal of Integer Sequences 2016 article. Let k = pr(K_{n,n}). Choose a labeling with sides A and B of size n using labels at most k. We may arrange 1 in B: if unused, replace a B label by 1; if in A, interchange sides. Let P be all prime divisors of elements of A. Every A label is greater than 1 and P-smooth. Every B label is coprime to every prime in P, by complete bipartite adjacency. Replace A by the first n P-smooth positive integers greater than 1, and B by the first n positive integers coprime to P. Both new maxima are at most k. The new sides are disjoint, cross-coprime, and have size n. Minimality of k implies their maximum is k. This is exactly the source's popop recipe, with no bound imposed on the size of P.

This is a short generic exchange/normalization argument directly from the source's definition. It does not supply a genuinely new method for determining k or selecting a small prime set. Under the binding credit standard, do not propose it as a discovery. No Lean investment justified.

## 337584: direct composition of printed propositions

Source: Selig–Smith–Steingrimsson, current arXiv v2. Proposition 2.6 gives the bijection Psi to permutations. Proposition 2.5 identifies the non-top row labels with the excedance bottoms of sigma = DE(Psi(T)); Proposition 1.6 makes DE bijective. Thus column labels are the nonexcedance bottoms of sigma. Proposition 8.1 (including its proof, read) identifies all-1 columns exactly with fixed points of sigma. Subtracting these sets identifies columns containing zero with strict deficiency bottoms of sigma. Inverting sigma turns each strict deficiency into an excedance, bijectively. The number is therefore A(n,k).

Every nonclassical ingredient is printed in the source, and the only bridge is inversion of a permutation. This is specifically the source-proposition-plus-classical-fact exclusion. No credit proposed. The published PDF route timed out in TLS handshake; no TLS relaxation or retry was used. Search indexing reproduces published Conjecture 53, but independent downloaded published-body evidence is absent.

## 325786: verification-range inconsistency, not a candidate

Source Definition 2 and Section 2.2 were read literally. A descent sequence starts with zero and each new digit is at most one plus the number of strict descents of its prefix. In co-RGC order, compare at the rightmost differing coordinate k; the order is descending there if suffix sum plus suffix length is even, and ascending if odd. The script independently encodes this as a lexicographic key read right to left.

At n=10, the consecutive words

    0 1 0 2 1 0 2 2 1 5
    0 1 1 0 2 0 3 2 1 5

have Hamming distance 4, changing one-based positions 3, 4, 5 and 7. Their changed span is 5 and their changed coordinates are not consecutive. The source's introductory adjacency definition requires changed positions to be adjacent, while Conjecture 1 claims verification through n=10. This is already inside that claimed range. The complete n=13 Hamming-distance sweep found no pair at distance >4. The span obstruction therefore must not be sold as a new beyond-range Hamming-distance refutation. The published-body download failed with 404; its search-index excerpt repeats the verification range and conjecture, but that is not a downloaded full published-body audit. No discovery credit or Lean endpoint proposed.

## 342507: repeated parts make the literal ordinary-pattern claim source-internal

The exact 4-variable, at-most-5-box comparison produced 38 mismatches among 125 distinct partition/composition cases. All were flagged polynomials whose minimal coset representative contains an ordinary 312 pattern. Already in three variables, lambda=(1,0,0) and w=s2*s1=312 give

    L_(0,0,1) = x1+x2+x3 + beta*(x1*x2+x1*x3+x2*x3) + beta^2*x1*x2*x3.

This is the one-cell flagged set-valued-tableau polynomial with flag3. The permutation is minimal in its coset (the images of the two zero positions are increasing), and contains312. However, the source's rectangular Lemma3.8/Theorem3.9 and Corollary3.11 already identify these polynomials as flagged Grothendieck polynomials. Thus a literal refutation uses the source's own rectangular machinery and a pattern check, precisely the zero-credit source-internal correction category. A correct parabolic/maximal-representative formulation is not investigated as a new target. The downloaded published body also retains Conjecture3.13.
