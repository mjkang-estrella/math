# Second-pass mechanisms, not solutions

No theorem below is offered as a full literal Lean endpoint. All finite computations are diagnostics. No new credit is requested.

## Rank 1: 365438, Zhao Conjecture 4.14

Read the actual introductory stack rule, Section 2.1 and Lemma 2.1, and all of Section 4.1.4, including proofs of Lemmas 4.15–4.17 and Corollary 4.18 (retained extracted lines 850–945). The underlined entries are adjacent in the stack, read top to bottom. With a fresh input a and old stack s, the new forbidden pattern occurs exactly when some adjacent old pair satisfies a<s[j]<s[j+1]. The simulation implements this rule, popping one element at a time until push is permitted; it does not use a classical/consecutive-pattern substitute. First input is never popped prematurely, so it equals the final output entry.

The source's smoothing offers a conditional induction route. If output ends in a<n and its penultimate entry is not a+1, swapping the adjacent values a,a+1 injects its fiber into the swapped output fiber. If its last two entries are (a+1),a, deleting the forced second input a+1 gives a size n−1 fiber. Assuming the size n−1 upper bound, this case is strictly below 2^(n−2) for n≥3. Thus a maximal fiber can be moved to an output ending in n, unless it was already below the desired bound. The source corollary must be read within that induction; it is not an unconditional proof of the conjecture. The n=2 base must be handled separately.

**Precise missing lemma:** every fiber whose first input is n (equivalently whose output ends in n) has size ≤2^(n−2). This, the source's two injective transformations proved at the algorithm level, and the source lower witness would yield the full all-n endpoint. Complement conjugacy gives the other map without separate credit. No proof of this missing lemma is retained.

Attempt A was a record-minimum block encoding. Proposed splitting the input tail at successive minima, reversing each block, and counting at most 2^(n−2) output cut subsets. It is FALSE. For input 51432, the actual output is 32415; the predicted block reversal is 23415. When 2 arrives, the old adjacent ascent 3<4 triggers a partial pop; the bottom-adjacent ascent is not the only possible obstruction. The source's reverse-layered characterization applies to its special decreasing-output witness, not arbitrary tails. This was caught before any formal theorem was written.

Attempt B deletes the second input and standardizes, attempting a recurrence through two smaller output fibers. It also fails as an immediate recurrence. For n=6 a single output fiber can lead to three distinct reduced outputs; for n=8 it can lead to six. Retaining the deleted value does not fix a binary bound: already n=4 gives three distinct (deleted value,reduced output) pairs. A weighted inverse-tree recurrence might still work, but needs a global budget invariant, not merely a two-branch assertion. No such invariant is proved.

The full simulation through n=8 tests every permutation, both adjacent-value bounds, maximum fiber count, and the incorrect block rule separately. Maxima agree with 2^(n−2) in this bounded range. This is not an all-n proof. At n=8 there are three maximum outputs, so a uniqueness shortcut is especially unjustified; the adjacent source-only Conjecture 4.19 is not promoted or counted as this target. No attempt is made to widen MathDB scope to that question.

Formalization burden: define finite distinct words, vincular avoidance and terminating right-greedy push/pop; prove output-permutation preservation and exact first/final relation; certify swap and deletion maps on fibers; prove the still-missing maximum-first upper lemma; show the literal lower witness and complement bridge; express maxima on all permutations. A finite table or an abstract fiber predicate cannot replace these bridges. Park with zero credit.

## Rank 2: 360074, Czédli Conjecture 4.2

Read actual definitions (4.1)–(4.6), Theorem 4.1 and Conjecture 4.2, and the proof's permutation-counting and minimization reduction (4.13)–(4.23), extracted lines 446–523 and 581–672. The primary source retains the unquantified r in its second conjectural inequality. The proof and tables compare against g_3. Do not refute a stray-r reading or silently broaden to every r. A literal endpoint needs a source-scope adjudication even if the minimization is solved.

Let F_n(t,x,y) be source f_{3,3} in (4.17), with t≥0,x,y≥1,t+x+y≤n−1. The source identity 2f_{3,4}=F(t,x1,x2)+F(t,x2,x3)+F(t,x1,x3) reduces the all-n minimization to

    F_n(t,x,y) ≥ F_n(floor((n−2)/2),1,1).

This stronger inequality is a sufficient target, not claimed equivalent to equality of the floored estimates. Exact integer minimization through n=65 in attempts.log verifies only that range, largely inside the source's published range to300; no new empirical coverage credit.

An all-n restricted-slice calculation DOES close: cancellation gives

    F_n(t,1,1) = 2(n−1)(t+1)!(n−t−2)!.

For two nonnegative integer factorial arguments of fixed sum, moving one unit from the larger argument to the smaller multiplies the product by (smaller+1)/larger≤1. Hence this slice is minimized at the balanced pair, including the two even-n minimizers noted by the source. This proves no all-(x,y) bound. The corresponding f_{3,4} candidate is 3(n−1)floor(n/2)!ceil((n−2)/2)!, consistent with (4.23).

Attempt A contracts x at fixed t. It fails: n=5 gives F(0,2,1)=44 < F(0,1,1)=48. Attempt B contracts x while increasing t. It fails: n=10 gives F(0,3,6)=756000 < F(1,2,6)=757440. These exact diagnostics explain why a one-coordinate descent is insufficient, rather than asserting that minimization itself fails.

Further factorization, with c=n−t−x−y≥1, is

 F=(t+x)! y! c! [binom(y+c,y)−2]
   +(t+y)! x! c! [binom(x+c,x)−2]
   +2(t+x+y)! c!.

Both bracket coefficients are nonnegative; however dropping them loses the needed balanced lower bound in the small x,y regimes. A successful proof needs a coupled balancing inequality keeping these terms, followed by source factorial/floor bridges and the strict comparison (with its r scope resolved). None is proved here. Park rather than package the slice calculation as the original conjecture.

## Rank 3: 382271, Bravo et al. Conjecture 4.24

Read the actual Type5 construction, Proposition 4.16 with proof, Corollaries 4.17–4.18, Theorem 4.20 with proof, and the full computational proof paragraph of Theorem 4.23 preceding Conjecture 4.24 (extracted lines 348–369 and 744–866). Theorem 4.23 already computes through n=200; reproducing smaller ranges is not new evidence for credit. Earlier classification theorem from reference [1] is not independently audited.

Set a=n−t≤b=n−s≤c=n−r. Then a,b,c≥1, a+b+c=n and c≤n−4. The polynomial is P=x^n−x^a−x^b−x^c−2. Since a+b+c=n, for x>1,

 P'(x)=x^(n−1)[n−a*x^(a−n)−b*x^(b−n)−c*x^(c−n)]>0.

P(1)=−4 and P tends to infinity, so there is exactly one root >1. The literal positive root is >1 because P≤−1 for 0<x≤1. This simple monotonicity does not establish distinct roots of different triples.

Attempt A (inherited irreducibility shortcut) is blocked in the actual admissible domain: n=6, a=b=c=2 gives

 x^6−3x^2−2=(x^2−2)(x^2+1)^2.

More generally a=b=c=d gives (x^d−2)(x^d+1)^2. Thus even the positive-root minimal polynomial can have degree only n/3. A generic degree>n−4 argument is false. Bounded exact factorization for n=6..30 records many cyclotomic factors; it does not certify no future collisions. SymPy factors are diagnostics only.

Attempt B exploits the shared sum of exponents and convexity. At n=3d the balanced triple's root is 2^(1/d). Jensen's strict inequality for x^u shows that any other triple with sum3d has x^a+x^b+x^c>3x^d=6 at that x, hence a strictly larger root. So balanced triples cannot collide; this is a restricted classical comparison, not the full target. Crossing triples, such as the source's (r,s,t)=(6,10,12) and (8,9,11) at n=14, remain outside a total majorization order. Equality of sum of exponents and equality of three powers at a single algebraic x do not force equal triples.

**Precise missing lemma:** for distinct sorted admissible triples at a fixed n, their polynomial gcd has no real root >1. A classification of noncyclotomic factors adequate to prove this, or a full sparse-relation uniqueness argument, is missing. Also needed for a Lean endpoint: algebraic root existence/uniqueness and the literal triple quantifiers (a graph-spectral bridge only if the endpoint is stated as digraphs rather than the primary polynomial conjecture). Park. No claim that this is currently unresolved in all literature.
