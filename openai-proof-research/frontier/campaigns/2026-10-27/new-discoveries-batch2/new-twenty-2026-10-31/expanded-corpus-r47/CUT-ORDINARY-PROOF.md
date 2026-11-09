# 353823: ordinary proof route; NO Lean endpoint; zero credit

This is an investigator's proof, using published Theorems 3 and 19 of Ellis–Thanatipanonda. It is neither independently reviewed nor accepted. Qualification/significance remains for root review: the new step is a weighted-bit potential applied to an already known sequence; a routine-consequence objection is possible. No claim of worldwide novelty.

## Exact scope and definitions

For any sets X of even integers at least 4 and Y of odd integers at least 5, both nonempty, put x=min X=2c, y=min Y, c≥2. Assume y>3x=6c. Let C={1}∪X∪Y. A cut d replaces one heap of size n by d+1 positive integer heaps summing to n. Normal play, disjunctive addition, xor of option values, mex recursion. Claim: G_C(n)=G_{ {1,2c} }(n) for EVERY positive n, including infinite X,Y. Only finitely many cuts are legal at a fixed n.

Source: arXiv:2203.02457v1, Definitions 1–2, Theorem 3, Lemma 18, Theorem 19 and its induction proof, Section 7 Conjecture 2. The author's published PDF was read through web extraction for the rule definitions and Conjecture 2; its direct local fetch timed out (no local PDF hash invented). The arXiv PDF is retained and hashed.

## Weighted-bit lemma

Write v=8q+4e2+2e1+e0, with e_i∈{0,1}, and define

    W_c(v)=12c q+(4c+1)e2+2c e1+e0.

This is the sum of the set binary digits of v with positive weights: 1,2c,4c+1,12c,24c,48c,... . Thus W(a xor b)≤W(a)+W(b): at each digit xor keeps a digit iff exactly one input has it; when both have it the left contribution is zero. Induction gives the same inequality for every finite list. This statement includes arbitrarily large integers, not a finite xor table.

Let g(n)=G_{ {1,2c} }(n). Theorem 3 gives g(n+12c)=g(n)+8. For the first 12c entries the blocks are

    (0,1)^c; (2,3)^c; 1,4,(5,4)^(c-1);
    (3,2)^c; (4,5)^c; (6,7)^c.

The low-digit potential values at v=0,...,7 are

    0,1,2c,2c+1,4c+1,4c+2,6c+1,6c+2.

For n=1,...,12c, direct symbolic substitution into the six alternating blocks gives

    1 ≤ n-W_c(g(n)) ≤ 6c.                         (★)

For clarity, in blocks 1 and 2 the deficit is one of 1,3,...,2c-1. In block 3 the exceptional first entry has deficit 4c; the second has deficit 1; subsequent alternating entries have deficits between 1 and 2c-1 (c≥2). In block 4 the deficits range from 4c through 6c. In block 5 they range from 4c-1 through 6c-2. In block 6 they range from 4c through 6c-2. These contain all entries, including c=2.

For arbitrary n=12c q+r, 1≤r≤12c, the theorem gives g(n)=8q+g(r), g(r)<8. Consequently W(g(n))=12c q+W(g(r)); the deficit is unchanged and (★) holds for every n.

## Extra odd cuts cannot hit the mex

Suppose n=h1+...+hp, all hi≥1, and xor_i g(hi)=g(n). From (★), W(g(hi))≤hi-1. Therefore

    W(g(n)) ≤ sum_i W(g(hi)) ≤ sum_i(hi-1)=n-p.

But (★) also says n-W(g(n))≤6c. Hence necessarily p≤6c. Every d∈Y has d>6c and therefore p=d+1>6c, a contradiction. No such new option hits g(n). This argument actually needs only the displayed part-count inequality; we do not claim extra mathematical scope as a separate outcome.

## Induction and mex bridge

Put C0={1}∪X. Theorem 19 states G_C0=g. Strongly induct on n. Each part of any legal option is strictly smaller than n, since there are at least two positive parts. The induction hypothesis makes every C-option's value equal to the xor of the base g-values of its parts. All C0-options are retained. Their mex is g(n), so they contain every value below g(n) and omit g(n). The added Y-options omit g(n) by the preceding argument. Their union therefore still has mex g(n). At n=1 there are no legal options and both values are zero. This proves the claim for all n, with no restriction on the cardinality of X,Y.

## Remaining qualification and formal obligations

No full literal Lean theorem is supplied. In particular, it is NOT legitimate to introduce g by the displayed formula and call that the actual game without proving the bridge. The missing formal prerequisites are a well-founded mex definition over all positive partitions; the exact arbitrary-c Theorem 3 formula for the {1,2c} game (or a different proof of (★) directly for that actual game); and Theorem 19's even-cut invariance (or formal Lemma 18 and its hypotheses). The xor potential and induction then close the literal endpoint. The primary base-sequence proof is long and contains case analyses; no axiom, placeholder or finite-table substitute has been inserted.

Bounded search found no Family B proof; that is not clearance. DDLP arXiv:1803.02621 Proposition 13 and Theorem 9 were read for their scope: they require finite AP-test hypotheses and do not themselves identify every Family B game with this base sequence. Published-version comparison of all possible successor papers and a significance review are unfinished. Omega's Family A formal body was read: it assumes cut 3 and proves a different sequence, so importing its result does not close this endpoint. Its game infrastructure may be reusable after an appropriate audited port; no upstream source was edited.
