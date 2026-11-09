# Disposition: exact prior-proof exclusion; no discovery nominated

Credit 0. This lane has no acceptance authority. Campaign counts remain 3/30 additional, 33/60 total. No Lean investment or PROOF.md is justified.

## Literal source and quantifiers

Terence Tao, *An integration approach to the Toeplitz square peg problem*, arXiv:1611.07441v2 (7 June 2017), Definition 6.3, Conjecture 6.8, Theorem 6.10, Sections 6.1 and 7. Actual published version: Forum of Mathematics, Sigma 5 (2017), e30, DOI 10.1017/fms.2017.23. The publisher PDF was successfully obtained; the same conjecture and equivalence occur on printed pp39–45. This is MathDB334668, not the neighboring four-curve record334666.

For each i=1,2,3 choose an arbitrary positive odd integer k_i and distinct real numbers y_(i,1),...,y_(i,k_i). Append y_(i,0)=y_(i,k_i+1)=-infinity. A list of m pairs, m=2 or 3, has noncrossing sums precisely when no conflicting infinities occur, all 2^m corner sums are nonzero, and the alternating signed count of the positive corner sums is zero. This is the actual Definition 6.3; the informal notion of nonalternating order alone does not suffice for three pairs.

Assume (i) every two same-parity edges in each row, with the second edge negated, have noncrossing sums; and (ii) every triple of edges with same-parity starting indices, one in each row, has noncrossing sums. The conclusion is

    S = sum_i sum_(j=1..k_i) (-1)^(j-1) y_(i,j) < 0.

All odd lengths and all real inputs are quantified. No small-length result is proposed. The original source already covers a row of length1, and reports an ad hoc length3 argument.

## Current public proof evidence: decisive full subsumption

Ali Naseri Sadr, *The Four Periodic Inscription Problem*, arXiv:2610.24376v1, submitted17 October2026. The actual complete HTML was retrieved29 October2026 at05:30 UTC. Read Theorems1.2/1.4, Corollaries6.1/6.3, and their Section6 proofs. Corollary6.3 explicitly identifies itself as Tao's Conjecture6.2. This is a much stronger exclusion than an abstract or registry-name match.

Its statement: three rectifiable embedded curves with vertical unit period and zero total quotient integral integral X dY admit points with equal imaginary parts and real parts summing to zero. It has no extra requirement of empty triple intersection. Its proof treats the common-intersection case separately, and otherwise applies the four-curve inscription result after three linear shears. Thus no common-point loophole remains.

Here is the complete parameter/coordinate bridge to the actual target:

1. For Tao's cylinder of circumference L and curves gamma_i with horizontal period L, lift each and map (x,y) to (X,Y)=(y/L,x/L). Reparameterize the lifts so translation by one parameter period adds (0,1). Simplicity, rectifiability, and one winding are preserved.
2. The total integral integral X dY equals L^(-2) times sum_i integral_(gamma_i) y dx. The cylinder quotient is crucial: this equality does not incorrectly integrate the multivalued horizontal coordinate as an ordinary function.
3. Naseri Sadr's Corollary6.3 then says that zero total area forces three lifted points having the same x coordinate and y coordinates summing to zero. Hence its contrapositive gives exactly Tao's symmetric area Conjecture6.2 on ALL polygonal inputs.
4. Tao's published Theorem6.10 gives the full finite Conjecture6.8. The relevant forward proof was read, not just its label: if S>=0, openness of finitely many strict sign constraints allows S>0 and distinct finite edge lengths. Tao constructs simple polygonal meanders with no simultaneous zero sum using Definition6.11 and Lemmas6.12–6.13. Their total integral is (L-4)S-C1-R, where C1 is independent of L,R and the closing graphs allow all sufficiently large R. First choose L large, then R=(L-4)S-C1. The area is zero, contradicting step3. This handles strict negativity, including the originally possible S=0 case.

This resolves the eligibility question negatively: the source endpoint already has a public proof chain dated17 October2026, before this lane. The bridge is an ordinary application of two public results and earns zero. This lane does not independently certify the Floer-homology foundation of the new paper. No claim of its earliest worldwide priority, external Lean replay, or original combinatorial proof is made.

## Substantive failed ordinary proof route: adjacent-pair deletion

Before closing the finite lead, pursued the natural induction on total odd row length. Deleting two consecutive entries preserves all subsequent parity signs. If their signed contribution Delta is nonpositive, then S=S_reduced+Delta, so an induction hypothesis S_reduced<0 would imply S<0. The missing assertion would be: every valid input with a nontrivial row has an adjacent pair with Delta<=0 whose deletion preserves BOTH source axioms. This assertion is false.

Take the exact integer rows

    A=(0,100,200), B=(0,20,40),
    C=(-1,-19,-41,-139,-121,-99,-201,-219,-241).

They are a scaled specialization of Tao's Section7 perturbative construction (epsilon=1, finite sums separated by at least20), not a new candidate family. All original axioms pass exact corner-sign evaluation. Their row alternating sums are100,20,-129, giving S=-9.

The only deletions with Delta<=0, using ONE-BASED starting index j, are:

| Row | j | Delta | first violated source condition after deletion |
|---|---:|---:|---|
| A | 1 | -100 | (ii), edge starts (0,0,0) |
| B | 1 | -20 | (ii), edge starts (0,0,0) |
| C | 2 | -22 | (ii), edge starts (1,1,1) |
| C | 5 | -22 | (ii), edge starts (2,0,4) |
| C | 6 | -102 | (i), row C, edge starts3,5 |
| C | 8 | -22 | (ii), edge starts (3,1,7) |

The new alternating sums in these six cases are91,11,13,13,93,13. In particular they are not smaller valid induction problems. Example: deleting the first two A entries leaves A=(200). At edge starts (0,0,0), the single finite corner sum is200+0-1=199>0, and every other corner is negative infinity. Thus the alternating count cannot vanish. This is an exact logical falsifier for the proposed greedy lemma, rather than failure to find a proof.

Some deletions do preserve the axioms, but every such deletion has positive Delta (100 or18) and gives no upper-bound induction. `checks.json` lists every one of the12 adjacent deletions. The bounded exact checker implements the literal extended-real corner rules, including zero-sum rejection and both parity classes. It enumerates at most eight corners per local test, not arbitrary permutations, meanders or unbounded grids.

A global proof by deletion would therefore need simultaneous changes to multiple rows, or quantitative information stronger than the sign of the removed contribution. No invariant supporting that stronger induction was established. The source's existing winding-number approach also explicitly fails to give a pointwise bound W12^0<=1 in general; that shortcut is not resurrected here.

## Scope of source/registry/history investigation

Read ancestor and batch rules; ledger accepted/candidate scopes; prior-campaign accepted/excluded families; NEXT checkpoints; r5/r7/r8 analysis summaries and r7 detailed report; Astra analysis r2/r3 rejection summaries; relevant first-batch strict novelty exclusions and parent-fresh-screen history. No prior campaign lane addressing334668 was located by targeted source-ID/topic searches. This is a bounded relevant-history check, not a claim to have read every historic file in full. All explicitly forbidden families were excluded before selection. Preliminary Handelman and finite-free-Stam leads were abandoned at source/prior-history checks; no mathematical discovery inferred from them.

Per instruction, no broad GitHub API traversal was attempted. Reused the recent r7 complete omega D5/Problems trees, complete OpenAI preprint subtree/current catalogue, count-ex-machina registry and their head receipts. The omega receipt is at67b4fae085cf19003a33f8027410c383b49e5046 (04:37:11Z29October); count atdbf673741a54c7dc9d88a6aec0e8148a538f4a3a (9September); OpenAI at7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (26October). These were NOT refreshed by this lane and are not presented as a complete05:30UTC repository census. Topic/ID screens are indexed-path/registry checks, not whole-code proof audits. No exact hit was needed to decide eligibility: the fresh17October primary paper explicitly states the subsumer.

The original immutable OpenAI metadata pinsfd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (8October); the source catalogue was consulted as a locator, not relied upon as live novelty evidence. Public web searches led to both actual source bodies. MathDB's search-result open label and empty solution count were deliberately ignored as novelty evidence. No direct MathDB requests were made in this lane. The nearby four-periodic-curve theorem is also public; no separate credit is sought for334666.

## Verification and missing gates

Run `python check.py` in this directory. It enforces512MiB address space,20CPU seconds and BLAS thread count1, and writes deterministic `checks.json`. It verifies all source axioms for the displayed finite input, all12 deletions, S=-9, and three exact polygonal shear-integral diagnostics. These are exact finite checks, not a proof of the all-input conjecture or certification of the external paper.

No eligible new theorem, full independent ordinary proof, literal Lean endpoint, paper, review or acceptance is asserted. No PROOF.md created. All writes stayed inside this lane. No children, git operations, public posts, uploads, contacts, accounts or browser tabs. Final obstruction is prior public proof plus an exact failed-induction witness, not an unresolved normalization or numerical sign.
