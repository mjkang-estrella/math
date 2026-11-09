# Full literal Conjecture 4 counterexample — uncredited

This is a finite, search-independent refutation of the universal statement, not a proof of novelty. It is an automatic separated-block extension of the source's own Table 1. No discovery credit is requested.

## Source conventions checked first

Ezerman–Meyer–Solé, *On Polynomial Pairs of Integers*, JIS18 (2015), Article15.3.5, https://cs.uwaterloo.ca/journals/JIS/VOL18/Ezerman/eze3.pdf, printed pp2–5: A and B are positive integers, not necessarily distinct. In Section2, A=sum(a_i 10^i), with ordinary decimal digits, and P(A,x)=sum(a_i x^i). A*=sum(a_i 10^(a-i)); a is the highest occupied place of A. Palindrome means A=A*. Polynomial means P(A,x)P(B,x)=P(AB,x). Proposition1 equates this to carry-free multiplication. Conjecture4, p5, imposes neither A nor B palindromic; it imposes no bound on lengths or product size.

The body does not explicitly exclude a zero units digit; we do not need to decide how to repair any resulting reversal involution claims. All six integers A,B,C,A*,B*,C* below have nonzero endpoint digits. No leading zero is supplied or lost. All polynomial coefficients come from their actual decimal expansions. The 2012 precursor, arXiv:1210.7593v2 updated2014-08-15, has the same C4 (its printed p4). Journal PDF SHA256: 07536739c05d45b78d36b298b45a45abf09a6f630dca1b510e624145efab4a97.

## Integer certificate

Set A=7000000070000007, B=858088. Then

```
7000000070000007 × 858088 = 6006616060066166006616
7000000700000007 × 880858 = 6166006616600606166006
```

The second line reverses each of the three integers on the first line. A differs from A* (the internal 7 moves from place7 to place8), and B differs from B*. Thus the hypotheses are satisfied exactly. The constant coefficient of P(A,x)P(B,x) is 7·8=56, whereas that of P(AB,x) is6. Therefore the polynomial identity fails.

Here is the entire forward multiplication certificate, least significant column first. Initial incoming carry is0; every line obeys s_i+c_(i-1)=d_i+10c_i. Column21 has zero convolution and discharges the final carry. All later columns are zero.

| i | s_i | incoming | d_i | outgoing |
|---|---|---|---|---|
|0|56|0|6|5|
|1|56|5|1|6|
|2|0|6|6|0|
|3|56|0|6|5|
|4|35|5|0|4|
|5|56|4|0|6|
|6|0|6|6|0|
|7|56|0|6|5|
|8|56|5|1|6|
|9|0|6|6|0|
|10|56|0|6|5|
|11|35|5|0|4|
|12|56|4|0|6|
|13|0|6|6|0|
|14|0|0|0|0|
|15|56|0|6|5|
|16|56|5|1|6|
|17|0|6|6|0|
|18|56|0|6|5|
|19|35|5|0|4|
|20|56|4|0|6|
|21|0|6|6|0|

`exact-checks.json` includes every reversed-product carry, both digit-polynomial vectors, seed and a second construction. `verify.py` independently reconstructs digits by divmod, reverses by place accumulation, and checks every carry and integer equality. No search or floating unsatisfiability result is an assumption.

## Structural mechanism and its novelty objection

The source already supplies 7·858088=6006616 and 7·880858=6166006. Write S=1+10^7+10^15 and S*=1+10^8+10^15. The three copies of the seven-digit product occupy disjoint positions. Reversing the resulting 22-digit integer reverses each seven-digit block and maps starting positions {0,7,15} to {0,8,15}. Hence A=7S, A*=7S*, C=6006616S and C*=6166006S*, which proves the displayed equalities without enumerating pairs.

More generally, the same argument applies to A=7(1+10^m+10^n), B=858088 for all m>=7, n-m>=7 and n!=2m. The blocks cannot overlap; the first factor is nonpalindromic precisely because its two gaps differ. The original nonzero carry block persists. This is ordinary block concatenation, so the infinite family and its fixed instance receive no separate novelty claims. Ninety exact parameter tests are diagnostics, not the proof of this universal construction.

A second control starts with the source's classical palindrome factors 7·88=616. Let U={0,1,3}, V={0,4,9}, A=7 sum_(u in U)10^(3u), B=88 sum_(v in V)10^(3v). All nine u+v are distinct, so AB consists of nine disjoint 616 blocks. Reversal reverses both exponent sets, preserving the identity. Neither set is centrally symmetric, so neither factor is palindromic. The constant coefficient is again56. This independently shows that asymmetric concatenation can remove both palindromic-factor restrictions. It is still the same automatic source-example extension, not a second outcome.

## Carry constraint reduction, with exact length quantifiers

For endpoint-nonzero factors let N=deg P(A)+deg P(B), D=P(AB), F=P(A)P(B), and let delta=deg D-N, which is either0 or1. Extend all arrays with zeros, and let c_i be the actual nonnegative outgoing carries; finitely many are nonzero, c_(-1)=0. Put H(x)=sum c_i x^i. The column identities give

F(x)-D(x)=(10-x)H(x).

Reversal commuting is equivalent to F(1/10)=10^delta D(1/10). If delta=0, H(1/10)=0; nonnegativity then forces every carry to be zero. If delta=1, it is equivalent to H(1/10)=(10/11)D(1/10). This is a complete necessary-and-sufficient carry bridge for this endpoint-nonzero scope; it does not classify all digit realizations. The witness lies in delta=1: lengths16,6,22. That extra product digit is an actual digit, is preserved by reversal, and is also present in the source's own Table1 seed. It is not a dropped-leading-digit artifact.

The source's Proposition14 is a related no-extra-product-digit result for (A,A*). Our generic reduction is an uncredited elementary carry observation. Neither it nor the counterexample resolves Conjecture11, whose two factors are constrained to be reversals of each other. No all-length proof of C11 is claimed.

## Prior-art status

The exact-author/title current arXiv screens return the same 2014v2 body, not a located later same-object proof. This is a bounded search, not priority clearance. Actual Sloane arXiv:1307.0453v4, first sections, uses carry-labelled Young graphs and restricted concatenations for N*=kN; actual Holt arXiv:1412.0231v4 Theorem1 and its digit/carry proof construct derived palintiples; actual Faber–Grantham arXiv:2108.13441v2 Section4 handles a+b=(ab)* by compatible two-sided carries. These are different predicates from A*B*=(AB)*. No complete published subsumption of C4 was located in those passages, and no claim is made that they explicitly state this witness. Their standard construction mechanisms, together with Table1 itself, are a strong routine-extension objection. Current public-registry heads were not cleared: the denied API/raw/codeload/diff/patch routes were not retried. Status: full mathematics, bounded source fidelity, novelty/substantive eligibility unapproved; zero requested credit.
