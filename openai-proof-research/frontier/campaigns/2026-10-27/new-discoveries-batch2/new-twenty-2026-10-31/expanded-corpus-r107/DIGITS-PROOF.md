# Candidate: MathDB 356756, full source Conjecture 2.4

Candidate only, zero accepted credit pending root and independent reviews. The source is Elsholtz–Klahn–Lipnik, arXiv:2211.02588v1, Section 2, Conjecture 2.4, and the open-access published version, Designs, Codes and Cryptography 91 (2023), 1443–1452, DOI 10.1007/s10623-022-01145-w. The defining equal-frequency set is in Section 2 immediately before Theorem 2.2. Both primary PDFs were retrieved with dated URL/status/SHA-256 receipts. The conjecture page was rendered and visually inspected.

Let p = 4k + 1, k ≥ 3, and h = 2k + 2. Thus D = {0,...,2k} ∪ {h}, with |D| = 2k + 2 = (p+3)/2. For n divisible by |D|, S(D,n) consists of the vectors over Z/pZ whose coordinates belong to D and contain each digit exactly n/|D| times. We prove that S(D,n) contains no nonconstant four-term arithmetic progression. In fact primality is unnecessary.

Define the integer potential

    E(t) = 4t² − (12k−2) ε(t),  ε(t) = 1 if t is even, −1 if t is odd.

The local assertion is that for a,b,c,d ∈ D with a−2b+c ≡ b−2c+d ≡ 0 modulo p,

    E(a)+E(d)−E(b)−E(c) ≥ 0,

with equality only when a=b=c=d.

First classify wraparound. The integer a−2b+c is a multiple of p and lies between −2h and 2h. Since 2h = p+3 < 2p, the multiple is −p, 0, or p. If it is p, then a+c=p+2b ≤ 2h=p+3, so b=0 or 1. The case b=1 requires a+c=4k+3, impossible: the only digits above 2k are h=2k+2, and h+(2k+1) is forbidden. For b=0, the only possibilities are (a,c)=(h,h−3) or (h−3,h). In the first, d≡2c−b=p−3, which exceeds h for k≥3. The second gives precisely

    (a,b,c,d)=(h−3,0,h,3).

If a−2b+c=−p, then b=h and a+c=3. The possibilities c=0,1,2,3 give d≡2c−h. The first gives the reverse exceptional progression (3,h,0,h−3). The second gives the missing digit h−1; the others exceed h. The same classification applied in reverse handles a wrap in b−2c+d when the first second difference vanishes. Consequently the only nonordinary progressions are those two displayed progressions.

For an ordinary integer progression with step s=b−a, the quadratic contribution to the gap is 16s². Its parity contribution vanishes: the first and third terms have the same parity and the second and fourth terms have the same parity. Hence the gap equals 16s², and is zero precisely for the constant progression. In either exceptional progression, the outer digits are odd and the inner digits are even. The square difference is 18−6h=9−3p, and the parity difference is −4. Therefore the gap is

    4(9−3p) + 4(3p−5) = 16 > 0.

Now let four vectors A,B,C,F in S(D,n) form an arithmetic progression. Their coordinatewise gaps are nonnegative by the local assertion. Equal digit frequencies make the sum of E over the coordinates identical for all four vectors; the sum of all coordinatewise gaps is therefore zero. Each gap is zero, so every coordinate progression is constant. Thus all four vectors coincide, a contradiction to a nonzero common difference. This proves the full conjecture.

# Formal semantics and endpoint

`lean/Digits.lean` defines `SourceDigit` with the exact two integer divisions in the source, and `SourceSet` using actual `ZMod p` vectors and the cardinality of each digit fibre. `same_histogram` and `sum_same` prove the equal-frequency-to-potential-sum bridge. `digit_bridge` connects p=4k+1 with the integer digit interval; `dvd_bridge` connects actual finite-field arithmetic with integer divisibility. `full_scope` proves equality of all four vectors. `mathdb_356756` retains primality, p≥13, p mod 4=1, and the dimension divisibility hypothesis. `no_affine_progression` applies this to actual vectors x+jr for j∈Fin 4 and r≠0. No finite search is imported into the proof.

# Substantive and novelty limits

The source Theorems 2.2 and 2.3 cover different progression lengths or the opposite modulus congruence class. Its Section 4 gives a general finite linear-constraint/reducibility framework, but does not give this uniform parity correction or a uniform certificate for Conjecture 2.4. The earlier Elsholtz–Pach paper's proof of Theorem 3.10 uses ordinary quadratic convexity on the unextended interval; that potential alone fails here, with negative gap on the exceptional progressions. The new ingredient in this candidate is the explicit parity correction and uniform wrap classification. Elsholtz–Lipnik concerns affine caps and weighted three-term relations. Relevant construction/proof passages were read, not merely titles. Whether this uniform bridge meets the campaign's substantive standard remains an independent/root decision.

Bounded live searches did not locate an exact resolution; no claim of worldwide novelty or comprehensive citing-paper coverage is made. Current Omega complete D5 and Problems path screens and OpenAI HEAD were checked, but registry proof bodies were not exhaustively read. The published source still states the conjecture; this is source fidelity evidence, not proof of current openness. No publication or external message was sent.
