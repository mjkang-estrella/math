# r252 sustained ternary exact-cardinality investigation

No full resolution of Grytczuk–Stankiewicz Problem 1, arXiv2011.12822v1, printed p8. The exact target remains: a finite word on three letters with exactly 80 DISTINCT terminal descendants under UXXV -> UXV, X nonempty. No claim about missing-cardinality infinitude is made. The source Table 1 word of length49 and count81 is an input benchmark, not a discovery. Counts9/39/next40 remain administrative context only.

The primary text, r250 SUMMARY/SCOUTING/discovery and exact checker interfaces were hash-bound before scientific reading. Immutable paths and SHA256 values are in immutable-bindings.json; no historical evidence trees were copied. The actual source constructions and proofs on pp3–7 were read. Theorem1 uses a square-free morphism to establish a LOWER bound, not an exact classification. Theorem3 uses F=xabaxababx and increasing square-free prefixes over {a,b,y}, obtaining i+1 terminals for F W1 ... F Wi on FOUR letters. That theorem does not settle the ternary question. Conjecture4 is already covered by classical free-band finiteness, as documented in r250; no outcome is claimed here.

## Mechanism A: all internal nodes, branch set algebra and finite grammars

For each word w, enumerate C(w), the set of one-step children. Compute R(w)={w} if C(w) is empty, otherwise union of R(c) over c in C(w). Length strictly decreases, so induction proves this recursion gives exactly all terminal words. Equal terminal words reached by different paths are merged.

known81-dag.json contains the complete 2928-vertex adjacency list and an 81-bit terminal mask for EVERY vertex. An independently implemented deletion of the second square copy, using start/end indices rather than the first routine's period/start order, checks every edge, reachability of every vertex, every terminal mask and absence of extra children. Thus the certificate proves completeness as well as reachability. This verifies an existing example only.

No internal node has cardinality80. Only the root has81; the largest proper descendant has65. The root has11 distinct children, with cardinalities45,38,56,16,65,45,35,43,22,25,46 in lexicographic child order. dag-analysis.json records all55 child-pair intersections/unions. Every child has zero indispensable terminals relative to all ten other children: deleting one root branch alone cannot remove any terminal. Some pairs already cover all81 (including a disjoint56+25 pair and a disjoint16+65 pair).

All2048 subsets of the11 children yield361 distinct terminal unions;56 subsets yield cardinality80, representing18 distinct masks, each missing a different terminal. union80-branch-plans.json records all56 branch lists and18 inclusion-minimal plans. The smallest plan uses four branches [0,1,6,7], omitting abcacbcabacabcacbca; its reversal-pattern counterpart [1,6,7,10] omits abcbabcacbcabacabcacbca. These are exact set-cover calculations, NOT words realizing80. A branching gadget must realize the selected union while forbidding every unintended branch; arbitrary union of descendant sets does not itself correspond to a word.

Two deterministic finite grammars were fully evaluated to closure, with no aborted candidate counted:

* Every contiguous interval BASE[i:j], 0<=i<j<=49:1225 parameter choices,50464 shared memo states, no80.
* u BASE v, where u,v are square-free ternary words of length<=2, including empty:100 parameter choices, no80. All root-child cardinalities are retained in context-grammar.json. Counts attained are22,35,36,39,40,41,42,43,44,63,68,69,71,72,73,75,81.

These exhaustive finite negatives do not show nonexistence at any unrestricted length. The next concrete construction target is the four-branch union above, rather than another random sweep.

## Mechanism B: exact reduction reflection, with a finite certificate

Let h be a uniform morphism of codeword length q>=2. The following sufficient conditions imply C(h(w))=h(C(w)) for EVERY finite word w:

1. No codeword occurs at a nonzero offset inside the concatenation of any two codewords.
2. At every split 0<r<q, either the length-r prefix map or the complementary suffix map is injective on the source alphabet.
3. C(h(w))=h(C(w)) for all source words of length at most5.

Proof. The forward simulation h(C(w)) subset C(h(w)) follows by duplicating whole blocks. Consider an arbitrary square of period k in h(w). If k<2q, its two halves together cover fewer than4q letters, hence are contained in at most5 consecutive codewords. Condition3 applies to that block window, with the unchanged surrounding context, so its resulting child is an encoded child of w.

If k>=2q, the first square half contains a full codeword. Its corresponding occurrence in the second half is also a codeword substring. Condition1 forces their starts to have the same phase modulo q. Thus k=mq. An aligned square directly gives a square of source blocks. For a square starting at a split r, label the overlapping source symbols a0,...,a(2m). Equality of the square halves gives suffix_r(h(a0))=suffix_r(h(am)), h(aj)=h(a(m+j)) for1<=j<m, and prefix_r(h(am))=prefix_r(h(a(2m))). (Condition2 implies the codewords themselves are distinct.) If the suffix map is injective then a0=am and a0...a(m-1) repeats. If the prefix map is injective then am=a(2m) and a1...am repeats. Deleting the indicated source square gives exactly the encoded result of deleting the original square: the surviving boundary pieces join as prefix_r(h(a0)) suffix_r(h(am))=h(a0). This proves the reverse inclusion. Repeated application gives R(h(w))=h(R(w)); injectivity of a fixed-length distinct-block code preserves cardinality. Empty words cause no exception.

For the three codewords A=abacabcbacabacbabc, B=abacabcbacbcacbabc, C=abacbcacbacabcbabc from source Lemma1, q=18. synchronization.json checks all27 ordered codeword triples and17 nonzero offsets and every split. Conditions1 and2 hold. code-reflection.json exhaustively checks all3279 nonempty ternary source words of length<=7, including all363 required for condition3. A separate independent checker recomputes the363 tests and both synchronization conditions. Thus the exact reduction-reflection conclusion is supported by an explicit finite certificate plus the universal argument above; square-free preservation folklore is not being substituted for reflection. This helper is not offered as a new source-question resolution or novelty claim.

The coding mechanism does NOT remove the fourth letter. We exhaustively generated all1392 square-free ternary words of length18 and tried adjoining each distinct one as a fourth codeword to these FIXED A,B,C. Of1389 new choices,74 fail split injectivity,88 fail synchronization, and1227 remaining choices already fail one-step reflection on a two-letter input. No choice survives. fourth-code-extension.json preserves the rejected candidates, reasons and explicit extra-child counterexamples for the1227 reflection failures. This excludes extensions under this sufficient certificate, not every possible four-to-three code, not longer codes, and not all reduction-reflecting morphisms.

Separator tests also distinguish the actual hypotheses. With c absent from both binary sides, all36 pairs of nonempty binary square-free sides give the expected single terminal. Reusing c with arbitrary ternary square-free sides of length<=4 fails the naive R(u c v)={u c v} identity in1271 of1521 cases; explicit failures are retained. No repeated-separator product identity is assumed.

## Prior-art scope and chronology

The target source is dated25 November2020. Early live arXiv API exact-title and joint-author searches on30 October2026 each returned only2011.12822v1. They supplied no actual follow-up body resolving80. The original complete construction/proof bodies were read before the experiments. This is a narrow negative search, not current-open certification. Registry head/content audits remain blocked by inherited API/raw/codeload/diff/patch denials; these were not retried. ScienceDirect and Google challenge routes were not contacted. The old inaccessible historical intervals remain parked. No browser, proxy, TLS-disable, public action, MathDB mutation or git operation was used. The complementary eight-family source-body screen and its limited historical audit are in SCOUTING.md.
