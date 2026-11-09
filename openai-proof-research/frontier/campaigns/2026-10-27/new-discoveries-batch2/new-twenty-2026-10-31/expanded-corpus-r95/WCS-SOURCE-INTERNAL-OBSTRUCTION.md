# 361538: literal generation obstruction and qualification stop

**Zero credit; no claimed accepted discovery or Lean endpoint.** The intended source scope/significance requires root adjudication. This route is stopped because the obstruction is a short bridge from constructions and counts already present in the primary source, and may reflect an omitted extension of a starting family.

The large search flagged k=562, then a backward check found the same issue at k=22, inside the source's claimed verification range. The following permutation is weakly consecutive:

```
22,3,4,5,6,7,8,9,10,13,12,11,14,15,16,17,18,19,20,21,2,1.
```

An independent direct checker tests all 22^3 triples (i,j,d), with d from 1 through 22, without the gcd CSP or residue-domain filters. It finds no violation of d|sigma(i) and d|(i-j) => d|sigma(j). Divisors above 22 cannot divide any value. A complete finite generator closure is separately retained.

Under the literal Section 3 rules at fixed length 22, this permutation is not generated. The four starting types give only identity, the 1-inversion (23 is prime), and the twice-twin-prime sequence (11,13 prime); the Sophie starting type requires odd length 2p-1 and is unavailable. Rule 1 is restricted to that Sophie family. For Rule 2, the only prime power satisfying p^c <= 22 < p^c+p^(c-1) is p=2,c=4, so only the values 8 and 16 can be swapped. Rule 3 reverses the full sequence. These operations commute and are involutions. Thus the entire closure has 3*2*2=12 permutations, as explicitly enumerated in the retained check. A generated permutation with endpoints (22,1) must be reversed identity with an optional 8/16 swap. Its second term is 21, whereas the witness has second term 3.

This discrepancy is not treated as a new significant discovery. Source Table 2 itself records N(22)=16, whereas its literal fixed-length generation rules above yield only 12. Moreover, the witness is obtained simply by prepending 22 to the source's Sophie starting sequence at length 21. The same mechanism explains the k=562 flag: prepend 562 to the source's Sophie sequence of length 561 (p=281, p+2=283 and 2p+1=563 are prime). It therefore looks like a missing even-length extension of a printed construction, rather than a new structural obstruction beyond the authors' experiments. The assignment excludes routine bridges from source ingredients and wording/domain corrections.

The additional search completed k=851..870 except the capped k=861 case, and found eight analogous ungenerated witnesses at k=862 (p=431). These are the same construction-omission family, not another discovery.

The improved search completed k=501..570 and verified membership in the implemented family except at k=562. It must not be reported as a clean verification of the source generation conjecture through 570. Likewise, the complete small CSP checks only the WCS definition and an auxiliary endpoint property, not generation membership.

No attempt is made to infer what the authors intended from their verification claim. Both the literal obstruction and the conflicting source evidence are preserved for root review. A Lean certificate for a corrected or surrogate generation predicate would not resolve that source-fidelity/significance gap.
