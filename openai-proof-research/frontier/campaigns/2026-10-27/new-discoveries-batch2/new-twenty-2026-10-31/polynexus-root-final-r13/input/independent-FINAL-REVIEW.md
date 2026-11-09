# Independent review of MathDB 352496

Recommendation: REVISE reporting only, then eligible for root acceptance consideration. Ordinary theorem, source-bound statement fidelity, and immutable production proof review PASS. No substantive mathematical defect found. Fresh validation PASS: 12/12 strict source rebuilds, 12/12 module-name kernel checker runs, 16/16 full-body audit partitions, and the separate safety and positive controls. All 282 module-origin production declarations and 7,003 transitive declarations are covered, with only propext, Classical.choice and Quot.sound. The 7,003 selected rendered type/body payloads equal the inspected immutable author output; both inventories and all shard receipts are delivered. Credit remains 0; current campaign 53/60 beyond 39. This is an independent review, not an implementation continuation or root acceptance.

## Exact statement and source decision

For every positive n, take zero and the n-by-n 0/1 matrices X(d,k,m), where d is integral and 1-min(0,d) <= k <= m <= n-max(0,d). Entry (i,j), at one-based indices, is 1 exactly when k<=i<=m and j=i+d. Count ORDERED pairs of NONZERO operands with ordinary nonzero matrix product. The reviewed identity is

120 psi(n) = (n+1)^7 - n^7 - (n+1)^3 + n^3,

as an integer equality, with the rational quotient as its consequence. The count is defined by a filtered finite set of actual matrices before the formula, not by the answer or a polynomial premise.

I independently adopt the source-bound interpretation of the literal cached record: its cited arXiv identifier, sextuple sum and exact conjecture formula specify the source's M_n. The record's loose words 'rook diagrams' and 'products' do not establish an autonomous theorem about all rook matrices or distinct output values. Those alternative interpretations are not endorsed. This qualification must accompany any root acceptance or public description; the raw record was not edited. Source §3 (4), §4 (17)-(24), §8 (53)-(55), and Remark3 agree between the cached arXiv body and actual publisher body (DOI 10.1007/s00233-022-10302-5). Remark3 expressly fixes x and counts the possible y. The identity multiplicities in (54) independently confirm ordered pairs. The publisher still presents Conjecture1; no analytic resolution is supplied there.

Source §2 explicitly defines N as POSITIVE integers; §4 first constructs the noncommutative examples for n>=2. The same printed entry/bound definition at n=1 gives zero and identity, and polynexus_one proves psi(1)=1. Thus positive-n includes the source conjecture's stated domain without asserting noncommutativity at 1. Lean Nat additionally contains 0: the existing polynexus_integer and polynexus_rational already quantify over all Nat, and fresh review-only controls prove psi(0)=0 and PSourceMn(0)={0}. The numerator at 0 vanishes. This is a canonical empty-size extension, not an assertion that the source's nontrivial-monoid convention holds at 0, and not a missing domain obligation or a credited correction. polynexus_literal's positivity premise is harmless, not answer-bearing.

## Source-to-Lean map and discharged obligations

Exact source hashes and declaration line numbers are in results/source-map.json; the following includes every production module in dependency order.

| Production module | Source/ordinary obligation | Actual checked definitions and proofs |
|---|---|---|
| PolynexusDiag | (4), one diagonal and genuine zero/identity | PCnd couples s+a=r+b; PBlk, PCnd_iff_t, occupied/corner entries, nonzero and PBlkId |
| PolynexusSrc | (18) one-based signed dictionary and uniqueness | PSrcLeg, PSrc, srcB_cast, srcCond_iff_PCnd, PSrc_eq_PBlk, srcDict_leg, inverse PBlk_eq_PSrc, PBlk_inj and PSrc_inj |
| PolynexusProd | Ordinary matrix sum, unique middle summand | PMulWit, PCnd_row_col_unique, PBlk_mul_entry and overlap necessity |
| PolynexusClose | (20)-(24), disjoint zero and genuine overlap witness | PBlk_mul_PCnd_iff, disjoint_zero, mul_closure, mul_nonzero, identity action |
| PolynexusSrcPrd | Source product is the actual block product | PSrc_mul_eq_PBlk_mul, source zero and nonzero implications |
| PolynexusPairs | (53), ordered operands without identification | PLeg, PB injection, PNZ actual image, PNzPairs filtered matrix pairs, psi, psi_eq |
| PolynexusCount | Operand cardinality by length | disjoint PLegFib, PLeg_card, legLin/legSq, PNZ_card_sq |
| PolynexusPartition | All zero pairs, strict left/right disjoint partition | PDisjT_union/complement/card, transpose PTri, reverse-transpose involution PSwapT, PZeroM_eq, partition_card |
| PolynexusGap | Unique gaps including adjacency and end boundaries | PToGap/PFromGap, legality, both inverses, PLeftM_card_gap |
| PolynexusGapCount | Full disjoint length fibers and outer multiplicities | PGT_mem/card, PGF_mem/card, PLengths, PGap_fibers/card_sum, PLeftM_card_sum |
| PolynexusEval | Entire finite convolution, casts, endpoint | PInner, auxiliary PQuartic, POuter, PDouble, PLeft_eval, rational/integer/positive theorems |
| PolynexusLiteral | Exact printed bounds and source operand-set count | PSrcLeg_printed, PSourceMn, PNZ_source, polynexus_literal, polynexus_one |

No rectangle proxy remains: equal offsets, not independent row/column membership, define entries. The signed dictionary a=k-1, b=k+d-1, e=m-k is exact because legal bounds justify each natural conversion; inverse d=b-a, k=a+1, m=a+e+1 recovers every legal triple. Printed min/max equivalence is an actual theorem, including negative d. The start and southeastern coupled corners prove parameter injectivity. PB's finite image therefore retains each matrix exactly once. PNZ_source is the required theorem identifying that image with PSourceMn minus genuine zero; the statement does not rely on an ordinary assertion of this identification.

For fixed outside row, at most one middle index j can contribute to ordinary multiplication. The proof explicitly sums that term, or proves all terms zero. With H=max(b,c), U=min(b+e,c+f), overlap produces output B(a+H-b,q+H-c,U-H). Its corner is (a+H-b,q+H-c), not the generally invalid (a,q). Legal endpoint bounds prevent truncated subtraction errors. Nat coefficients are faithful to the source's usual 0/1 inner products because at most one term is 1; no Boolean multiplication or cancellation hypothesis is substituted. The same observation gives ordinary scalar transport to any nontrivial unital semiring, but no general-semiring transport theorem is claimed as an exported production result. PSourceMn is an extensional source set, not a bundled Lean Submonoid; closure follows from the proved matrix formula and legal inequalities. A bundled submonoid instance and exported signed product-parameter theorem are not required for, and are not claimed by, the cardinality endpoint. In PolynexusClose output legality inequalities also occur as local proved facts in mul_nonzero, rather than a separate exported closure-with-membership interface.

## Independent ordinary counting and finite evaluation

A legal operand is uniquely a pair (I,J) of nonempty intervals of equal length, with increasing translation I->J. For X=(I,J), Y=(K,L), the ordinary product is nonzero iff J meets K. There are T=sum_(a=1..n)(n-a+1)^2 operands, so 6T=n(n+1)(2n+1), by the zero-base and consecutive-difference square-sum induction. No arbitrary rook diagram is inserted.

Disjoint J,K have exactly one strict ordering. Reverse order and transpose BOTH operands: ((I,J),(K,L)) maps to ((L,K),(J,I)). The new middle intervals are K,J. This involution exchanges strict left and strict right cases, with no commutativity assumption. If D counts the left class, disjointness and exhaustiveness give psi+2D=T^2 as a natural-cardinality identity.

Fix length-minus-one coordinates e,f, with e+f+2<=n. Unique gaps satisfy g0+g1+g2=n-e-f-2. The starts of the outside intervals are independently chosen in n-e and n-f ways. Gap g1=0 means adjacent, disjoint intervals, whereas equality of the occupied endpoints belongs to overlap. The gap inverse recovers all six parameter coordinates; no matrix products are quotiented. With t=n-e-f-2, the first two gaps have g0+g1<=t, and twice their triangular cardinality is (t+1)(t+2). PGF is used only under its explicit legal-length hypothesis when identified with a gap fiber. Fibers are disjoint by their e,f coordinates.

Reindex by m=n-e-1 and k=n-e-f-2. Then 0<=k<m<n; inverse e=n-m-1, f=m-k-1 is legal and unique. Moreover n-e=m+1 and n-f=n-m+k+1. Thus

2D = sum_(m<n) sum_(k<m) (k+1)(k+2)(m+1)(n-m+k+1).

These are rational polynomial factors after justified casts; in particular the n-m in this displayed evaluation is rational subtraction. PDouble proves the actual finite-set reindexing, including empty boundary sums.

For rational c, put F_m(c)=m(m+1)(m+2)(4c+3m-3). Its base is zero and its consecutive difference is 12(m+1)(m+2)(c+m), proving PInner by induction. Put A(m)=m(m+1)^2(m+2). The quartic-sum antiderivative G(n)=n(n-1)(n+1)(n+2)(2n+1) has difference 10A(n), proving 10 sum_(m<n) A(m)=G(n). Finally S(n)=sum_(m<n) A(m)(4n-m+1) satisfies

S(n+1)-S(n)=4 sum_(m<n) A(m)+A(n)(3n+5).

This recurrence and the quartic identity prove 30S(n)=n(n-1)(n+1)(n+2)(19n^2+19n+6). Substituting c=n-m+1 in PInner gives 12 times the double sum equal to S(n). Therefore 720D is the displayed sextic polynomial. This is the implemented finite-induction route; the earlier formal-series/binomial plan is not a missing dependency.

Writing 36T^2=n^2(n+1)^2(2n+1)^2 and subtracting the D contribution gives

120psi=(10/3)(36T^2)-(1/3)(720D)
=7n^6+21n^5+35n^4+35n^3+18n^2+4n,

which is exactly (n+1)^7-n^7-((n+1)^3-n^3). All subtractions here are in Q or Z; equality is reflected back into Z, not truncated in N. The zero-base finite inductions cover every n, and the positive quotient follows from nonzero 120. These identities were checked by mathematical reasoning and kernel proofs, not an external mathematical program or finite-value inference.

## Adversarial controls and objections

The fresh ControlsV2 file is review-only and is absent from production imports. It proves negative-shift source dictionary agreement, the full diagonal off-diagonal zero, overlap at a shared occupied endpoint, zero for adjacent singleton intervals, the invalid (a,q) corner being zero in a genuinely nonzero product with its corrected corner equal to 1, n1 and canonical n0, and the all-Nat rational quotient. NegativeEndpoint changes the cubic sign; NegativeRectangle asserts a filled-square off-diagonal entry. Both end at False and fail as expected. They demonstrate meaningful rejection rather than missing imports or timeouts. The initial Controls failed only on deprecated if_pos/if_neg warnings; its source/receipt are retained, and V2 uses ite_eq_left/right. Production was never repaired.

All inherited old rectangle and uncoupled witness objections are resolved by actual definitions and proof bodies. The source-set cardinality objection is resolved by PNZ_source and injection, not labels. A full-rook or distinct-output reading remains expressly excluded from the recommendation. No conclusion-bearing assumption, unproved series identity, hidden finite enumeration, or new axiom was found.

## Manuscript and bounded significance/prior review

The full immutable input/author-manuscript.md was reviewed against all twelve production sources. Its mathematical statement, complete gap count, finite evaluation, coefficient choice, source binding, n1 treatment and formal coverage are adequate. Its explanatory induction steps match PInner/PQuartic/POuter. 'Two finite induction identities' should be understood as the two principal summations with the auxiliary quartic identity explicitly shown, not as a count of exactly two theorem declarations. No substantive rewrite is requested.

Required reporting erratum for root: the last validation paragraph says the campaign remains 52/60. For the present handback the assigned count is 53/60. This review leaves the immutable manuscript unchanged and records its exact SHA256 in results/352496-gates.json. Other historical copied author/review metadata with 52/60 remains historical, not current status. No PDF is generated; the optional faithful typesetting was omitted, so there is no PDF skill marker, PDF delivery or unperformed render/visual-QA claim.

I read the actual companion publisher mathematical body (DOI 10.1007/s00233-023-10393-8) and complete copied 2014 partial-isometry paper, not only their abstracts. The companion allows real parameters; integer restriction recovers M_n, but real scaling generally fails to preserve the integer lattice. Its groupoid Corollary4 requires equality of intermediate supports, stronger than overlap. Its height/rank, Green-relation, ideal, root, Brandt and Sierpinski-rank results do not supply the finite ordered-pair incidence convolution. The 2014 ODP_n permits domains with holes: identity restricted to {1,3} already distinguishes it from M_n for n>=3. Its Proposition2.4 and Theorem2.6 count individual maps, and §3 counts D-classes via internal domain/image gaps. Those are not the three exterior/middle placement gaps weighted by two independent outer intervals needed here. Rank marginals do not recover intersection incidence. Neither named prior body provides a completed implication to this target.

The strongest routine-corollary objection is that the source multiplication criterion already exposes interval overlap, and the remaining tools are elementary. My judgment is a qualified significance PASS: the full constrained-parameter transport, ordered multiplicities and weighted all-n evaluation are the substantive step resolving the actual source conjecture; no named prior theorem reviewed supplies them. This is not credit for formalization or an endpoint correction. Root retains the campaign significance decision.

The copied current-prior review and current-root/delta limitations were read. Registry heads/path metadata and search non-discovery do not clear entire trees or commit histories; changed comparison bodies are unavailable. OEIS A083200 access was denied earlier and not retried. I made no network request and claim no fresh global novelty or chronology verification. Within the supplied bounded material, no concrete applicable earlier proof was identified; unknown literature is not an invented mathematical HOLD. Root's separate prospective prior qualification remains necessary at its stated limits.

## Execution, trust and handback

Bootstrap and frozen-before ran first in the exact required order. All 375 frozen bindings initially matched. An empty review build and all twelve source SHA256s were observed in the live capped inventory output before the first compile; results/setup-evidence.json references that contemporaneous transcript rather than fabricating a predated file. All twelve modules were then freshly compiled, and all twelve module-name leanchecker invocations passed. LEAN_PATH has only this lane's fresh build and the pinned upstream packages. Toolchain reports Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; the assigned mathlib pin is d13f23b723b8a846827a245b89c10fc7d3f11612. No git operation rechecked or changed that supplied upstream pin.

The independent full audit selects roots by module origin, not namespace, and traverses types AND values with allowOpaque=true. Thus private/generated declarations and theorem values are covered. All sixteen disjoint hash shards traverse the entire closure and print selected unabridged types/bodies, with pp.all, proofs, deepTerms and privateNames enabled. A separate Safety traversal rejects non-safe definition safety as well as unsafe constants. Production source scanning finds no sorry/admit/axiom/unsafe/partial/native_decide/extern/implementedBy tokens, and source imports are pinned upstream or the twelve immutable modules. This does not audit upstream mathematical truth; kernel checking and allowed axioms establish the certificate's dependency basis. Audit tooling is metaprogramming outside production, not an extra theorem assumption.

The author r11 full-body output was independently inspected and hash-bound to its manifest; abbreviated and CPU-limited raw attempts remain nonfinal historical evidence. Fresh execution, body-output coverage and author/own comparison are separately recorded in the final audit results. Human mathematical review covered every production proof and endpoint; I do not claim manually reading every expanded upstream kernel expression. Kernel checker and exhaustive dependency traversal supply that part of the evidence.

Every substantive reader/writer/compiler/checker/audit/bookkeeping operation used the unchanged supplied runner and writer. Initial output-interface/inline-syntax/working-directory failures and the deprecated-control warnings are preserved and detailed in results/read-resource-inventory.json. There were no changed caps, unchanged failure loops, external math programs/numerics/enumeration/CAS/solvers, children, fallback model/provider, network, installs, git, external messages, publication, shared-ledger or parent/dependency/immutable-source writes. The runner's own lane tmp/cache locations were used only as supplied environment overrides. Reaped process groups and per-run sampled resources are recorded; no whole-process/cgroup or aggregate concurrent CPU guarantee is inferred.

The final manifest covers actual files and completed receipt JSONs, with named noncircular exclusions for itself and the sealing/verification terminal log/receipt/result. Its independent verification and frozen-after are delivered beside this report. Root integrity counts and this technical recommendation confer no acceptance or independent campaign credit. The remaining root action is to adjudicate bounded source/prior/significance qualification and the reporting/process errata, then accept or decline; this reviewer does not modify any ledger.
