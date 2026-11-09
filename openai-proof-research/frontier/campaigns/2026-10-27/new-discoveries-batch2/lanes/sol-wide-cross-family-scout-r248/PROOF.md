# Literal four-attractor conjecture: counterexample

Provisional ordinary-mathematics resolution, not an acceptance or priority claim.
Source: Lubomíra Dvořáková and Veronika Hendrychová, *String attractors of Rote sequences*, arXiv:2308.00850v5, 15 September 2024, Section 7, p.15. The question asserts that every pseudopalindromic prefix of a binary generalized pseudostandard sequence has a string attractor of size at most four. Definitions 1 and 3, p.3, specify the literal domain and closure operation. Theorem 8 addresses the restricted all-E case, not arbitrary mixtures of E and R.

All positions below are zero based. Write R for reversal and E for reversal followed by binary complementation. Starting from the empty word, append the letters 0,0,1,0,1 and take closures E,E,E,E,R, respectively. This produces

    01
    0101
    0101100101
    010110010101100101
    w = 010110010101100101101001101010011010.

Thus w has length 36 and is a palindrome. Each closure is shortest: the longest E-palindromic suffix lengths at the first four steps are 0,2,0,4, and the longest R-palindromic suffix at the final step has length 2. These claims can also be checked directly by the supplied closure code. Extend the finite directive arbitrarily to infinite binary letters and antimorphisms; lengths strictly increase, so the resulting infinite sequence exists and has w as one of its defining pseudopalindromic prefixes. No periodicity, normalization or recurrence hypothesis in the source excludes this directive.

For a factor f let C(f) be the union of all positions in all its occurrences in w. Every attractor must meet C(f). The following are exact occurrence sets; an interval denotes all integers between its endpoints.

|factor|C(f)|
|---|---|
|001010|[5,10]|
|010101|[6,11]|
|101011|[7,12]|
|001011|[13,18]|
|101101|[15,20]|
|110100|[17,22]|
|110101|[23,28]|
|101010|[24,29]|
|010100|[25,30]|
|1100|[3,6] union [11,14]|
|0011|[21,24] union [29,32]|

The nine six-letter factors each occur exactly once. The last two factors each occur twice. These occurrence claims follow by scanning the displayed word at starts 0 through 30 or 32; `verify_attractor.py` independently constructs occurrence sets from literal substring comparisons.

Suppose an attractor Γ has at most four positions. Set A=[5,12], B=[13,22], C=[23,30]. The first, fourth and seventh rows force Γ to meet these three disjoint blocks. A block containing exactly one chosen position must have that position in the intersection of its three six-letter intervals: respectively A0=[7,10], B0=[17,18], C0=[25,28].

There are four exhaustive possibilities, including attractors of size three by padding to four positions.

* Each block contains just one chosen position. Those three positions are in A0,B0,C0 and avoid both C(1100) and C(0011). A fourth position would have to meet both of these disjoint sets, which is impossible.
* A contains two chosen positions. The sole B and C positions belong to B0 and C0. None of these four positions can meet C(0011), since that set misses A, B0 and C0.
* C contains two chosen positions. Symmetrically C(1100) misses C, A0 and B0.
* B contains two chosen positions. The sole A and C positions belong to A0 and C0. Meeting C(1100) forces one B position into [13,14], and meeting C(0011) forces the other into [21,22]. Neither meets [15,20]=C(101101); the A and C positions do not meet it either.

All cases contradict the attractor condition. Therefore γ(w)≥5. This already refutes the full universal source endpoint. For completeness, {5,10,18,21,28} is an attractor: direct checking of every distinct factor supplies γ(w)≤5. The lower-bound proof does not depend on that upper check, an optimizer, a complexity estimate, or extrapolation from a finite sweep.

The search and independent flat enumeration of all 58,905 four-subsets are diagnostics of this proof. Exact optimum elsewhere and a sharp universal bound for the whole family remain unclaimed.

## Source-method bridge and novelty limits

The tempting mixed four-position rule using longest R/E prefixes followed by each letter fails already at 01001101; its positions {1,2,3} miss a factor. Hence simply uniting the source's pure-closure boundary rules does not prove its general conjecture. The completed replacement is the occurrence-block obstruction above, not a claim based on search speed. The source's existing 2/3-position theorems remain consistent: our directive mixes E and R.

Schaeffer–Shallit2012.06840v6 Theorem2 is a general decidability method for automatic sequences; its proof translates attractors to a first-order formula and gives no four-bound for all generalized pseudostandard directives. Banbara et al.2602.16152v3 and Faro–Marino–Pavone2610.10950v1 classify canonical Thue–Morse words; they do not address arbitrary mixed closures. Minimal-unique-factor and hitting-set methods are classical. Whether this application crosses the campaign's substantive threshold requires independent root review. Current arXiv query results located no matching general-family refutation; full public proof registries, all citing bodies and worldwide priority are NOT cleared. No automatic count or acceptance follows.
