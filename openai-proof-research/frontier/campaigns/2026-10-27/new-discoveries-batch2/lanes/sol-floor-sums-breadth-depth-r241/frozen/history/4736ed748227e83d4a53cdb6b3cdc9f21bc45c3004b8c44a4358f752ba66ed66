# r77: higher-parameter PECK remains unresolved

Credit 0. No full ordinary proof or source refutation; no PROOF.md, formalization, paper, or nomination. Root alone accepts/counts. Observed ledger: 7 additional, 37 total, next 38.

## Selection and early duplicate gate

Read ancestor and batch AGENTS, NEXT, ledger and prior-campaign-context. Initial broad terminal listings were accidentally truncated; retained filename inventories replace them. All-date rg -l searches cover all .md/.json filenames, without limiting to SUMMARY or discovery reports. Saved early-duplicate-filenames.txt had a noisy bare-number 15031 match; exact-duplicate-filenames.txt removes that ambiguity. shankar-duplicate-filenames.txt and object-duplicate-filenames.txt include author, source ID, PECK, subexceedant and kernel-refinement objects. The lists are evidence of bounded searching, not evidence of global novelty.

Actual first-campaign record read before investment: 2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing/Problems/liang-sagan-2026-pinnacle-middle-order.md. It gives a public all-n>=6 no-upper-bound refutation of Liang–Sagan Question 8.6(a). Do not rediscover it. The corresponding Library/Words/shankar2026canon.md and current pinned Lean body were read: they concern Canon-permutation Q moments, not the present poset. The first-campaign r40 working file was read and concerns metric Blaschke, an unrelated broad-keyword hit. r23 discovery says the old Shankar Eulerian real-rootedness lead has prior-resolution indications. r52 SUMMARY and discovery identify the already-investigated Leake–Mohammadi Yekta Question 1.7; do not reopen it as fresh.

Three initial source leads were screened at author/source level: Liang–Sagan 2408.02782v2, Leake–Mohammadi Yekta 2609.39917v1, and Shankar 2508.12467v1. The first two fail freshness for the indicated targets; powered Eulerian real-rootedness is publicly resolved. Only one new question received sustained work: the distinct order-theoretic Conjecture 1 in Shankar 2609.15651v1. This is not an accepted-family variant, and no claim of new-to-literature status is made.

## Exact full target and closest theorem bodies

Primary source: Umesh Shankar, *Multivariate stability of powered triangular recurrences and parametrised Eulerian polynomials*, https://arxiv.org/html/2609.15651v1, 14 September 2026; DOI 10.48550/arXiv.2609.15651. Abstract history read on 29 October lists v1, submitted 14 September 14:34:13 UTC. Archived HTML bytes and SHA256 in http.json.

A function f:[n]->[n] is subexceedant if f(i)<=i for every i. Its kernel is its partition into equal-value classes, and bl(f) is the set of their minima. Q(n,l) consists of ordered l-tuples with a common bl set. The strict order (Definition 1.4) requires proper kernel coarsening in EVERY coordinate; add equality. Different labelings with identical kernels are incomparable. Rank is |bl|-1, with total rank n-1.

Conjecture 1 quantifies over EVERY integer n>=1 and EVERY integer l>1: Q(n,l) is PECK. PECK means rank-symmetric, rank-unimodal, and strongly Sperner: for every s in [1,n], the largest union of s antichains has the sum of the s largest rank sizes.

Actual Theorem A(ii)/Definition 1.4/proof, Proposition 1.2/proof, Theorems C/E and Section 5.1–5.3 proof bodies were read early. The source supplies symmetry/unimodality and the l=1 symmetric Boolean/chain decomposition and sl2 operators. It explicitly explains why odd-path synchronized flips for l=2 need not be comparable. It reports normalized-matching verification to n=8,7,6 respectively for l=2,3,4, and symmetric chains to n=7 for l=2. Recomputing those cases supplies no new outcome. The needed new content would be uniform strong Sperner, not real-rootedness or a finite instance.

## Attempt: transport through fixed block-minimum fibers

For B containing 1, let F_B be the subexceedant functions with bl=B. A tempting route is to couple uniform F_B to uniform F_C along refinement whenever C=B union {v}. Such a coupling tensorizes to l independent coordinates. One could then mix these couplings using a transport between B-types, whose weights are c(B)^l. This would give normalized matching globally, a stronger sufficient condition for the desired result.

The required local assertion is false. At n=4, B={1,3}, C={1,2,3}. F_B has four functions: 1121,1131 with kernel {124}|{3}, and 1122,1133 with kernel {12}|{34}. F_C has three functions: 1231,1232,1233, with kernels {14}|{2}|{3}, {1}|{24}|{3}, {1}|{2}|{34}. The two functions in the second lower class can refine only to 1233. A uniform refinement coupling would have to transport mass 1/2 into an upper point of capacity 1/3, impossible.

For EVERY l>=1, the subset of F_B^l having kernel {12}|{34} in every coordinate has 2^l points out of 4^l, hence mass 2^-l. Its neighbors in F_C^l consist solely of the tuple (1233,...,1233), of mass 3^-l. Since 2^-l>3^-l, a uniform coupling is impossible for every tensor power. This is an ordinary argument about the failed route, not a refutation of the full Q(n,l) claim: neighbors in other C-fibers remain available.

## Exact diagnostics and further route failure

check.py enumerates functions through n=6, compressing only label twins having identical kernels and hence identical neighbor sets. Flow capacities retain all multiplicities. For each B<C of adjacent sizes it tests normalized matching via exact integer max flow. Counts of passing/failing local pairs are (1,0),(4,0),(11,1),(25,7),(52,28) for n=2,...,6. The first obstruction above has capacity 10 of required 12.

Then the code permits type edges only when the single-coordinate fiber has uniform refinement coupling, and tests type transports for l=2,...,30. Of 435 diagnostics, 145 fail; already n=5,l=2, block counts 2->3 has capacity 118260<132840. Thus even selectively mixing only uniformly admissible local edges does not repair the route. This finite failure concerns the restricted construction only.

tuple_check.py separately tests ALL actual simultaneous-refinement edges at n=5,l=2. The ranks have sizes 1,180,738,180,1. All four normalized flows saturate, with capacities 180,132840,132840,180. Compression retains 1,85,147,30,1 kernel-tuple nodes and weights their label twins. Uniform weighted node coupling can be lifted to the actual elements because every adjacent pair of kernel-tuple classes is complete bipartite. These checks agree with the source's previously reported range; no new universal proof or credited instance.

## Precise remaining gap, strongest objection, falsifier

The full missing result is strong Sperner for arbitrary n and l>1. A concrete stronger sufficient lemma would be: for EVERY n,l,k and EVERY subset X of rank k in the literal Q(n,l), |N(X)|*|Q_k| >= |X|*|Q_(k+1)|. No such lemma is established. A proof must redistribute flow across different block-minimum types in a way depending on the particular kernel tuples; product couplings with uniform conditional fibers are insufficient. An order-raising Lefschetz operator as in source Theorem 5.1 is an alternative, also absent.

Strongest objection: failure of a proposed conditional coupling says nothing negative about full strong Sperner. Our positive global diagnostic emphasizes that distinction. A source falsifier would be literal n,l,s and s antichains whose union exceeds the s largest ranks (s=1 suffices if found). A Hall violation refutes the stronger normalized-matching route only; it need not refute PECK.

## Prior-art and access limits

Read-only complete inventories reused exactly at supplied heads: Omega70af54071bfd4ac098619a9db8c16bb6f7aced11, OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, observed 17:20:12 UTC 29 October. No new head refresh and no git operation. registry-path-matches.txt saves 991 bounded lexical paths (many triangular/analytic false positives). Exact Shankar/subexceedant/PECK path strings did not identify a same-target settlement; that is not body-level clearance. Current matching Canon Q source and actual Lean endpoint were fetched via pinned raw HTTP and read, establishing a different-object result. Blueprint was never treated as Lean. OpenAI CONTENTS read at the supplied snapshot; no whole-registry semantic audit or priority PASS. Web queries for exact source/PECK and synchronized/kernel-refinement Sperner found the primary paper and secondary summaries, no primary settlement in returned results; secondary summaries are not relied on.

All archived direct requests HTTP200, with no challenge markers detected, no API use/retries/proxy, and no account/browser/contact/post/upload operations. Acquisitions use a 3MB per-response cap, streaming hashes. Helper runs use copied recent capped_run.py, AS512MiB, process-group RSS512MiB, aggregate sampled CPU210s, wall230s, 40ms sampling and BLAS1. All guards exit0. The initial uncapped shell context searches/listings and shell file writes are administrative, not experiment scripts; initial overly broad/truncated terminal output is a retained deviation, not concealed. No other-lane or shared writes.
