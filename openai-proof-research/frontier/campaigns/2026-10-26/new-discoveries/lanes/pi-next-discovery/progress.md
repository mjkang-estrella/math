# pi-next-discovery lane progress

Research sub-agent: Pi (GLM). Date 2026-10-26. Standard speed, no children, no external posting.

## Phase 1 — audit of parent Grassmannian proposal (MathDB 365199 / Machacek 2410.06177v2)

Read in full: source text (880 lines), live MathDB record `sources/365199-live.json`
(solutions/human_solves/model_attempts/comments/attachments all empty, progress null),
parent README, run-words.json, rref-cross-check.json.

### Audit result of the proposed rank-3 F3 classification argument

The core no-repetition lemma is **correct and simpler than stated**:

1. In RREF rank 3 over F3, pivot columns are e1,e2,e3. For a post-last-pivot
   column v=(a,b,c): minors {e1,e2,v}, {e1,v,e3}, {v,e2,e3} force c, b, a in
   {0,1} respectively (F3 squares = {1}). So post types are the 7 nonzero
   (a,b,c) in {0,1}^3 (sign placement immaterial).
2. Two *distinct* nonzero types are automatically linearly independent:
   w = −v is impossible inside a single binary orthant (would force v = 0).
   This is stronger than the README's dependent-case discussion.
3. If a compressed post-word repeated a type v after a different type w: a
   2-dimensional span cannot contain all three e1,e2,e3, so some e_i has
   det(e_i,v,w) = d ≠ 0. The two maximal minors {e_i, v, w} and {e_i, w, v}
   (position order) have determinants d and −d = 2d; one of them equals 2,
   a non-square in F3. Contradiction. Hence every type occurs at most once.
4. Compression/expansion: a maximal minor of the expanded matrix (zeros
   inserted, adjacent duplicates) is 0 if it picks equal columns, otherwise
   equals the corresponding minor of the compressed word; so expansion
   preserves positivity and (skeleton, nonzero-position set) → matrix is
   injective. The count formula sum_L n_L · sum_m C(n,m)C(m−1,L−1) then follows
   once the skeleton set is proved complete.

### Why I do NOT pursue it to a counted discovery

Even fully proved and formalized, the endpoint is |Gr^≥0_{3,n}(F3)| for all n —
a **single special case** (one rank, one field) of the still-open Conjecture 2.3
(log-concavity for all k, n, all odd q). The campaign counting standard excludes
special-case counts, and the task instruction explicitly forbids accepting a
narrow enumeration because the full conjecture is hard. The general-q
generalization of the argument also fails: for larger q the post-pivot orthant
(a,−b,c) with a,b,c ∈ Fq^≥0 contains dependent distinct projective types and the
no-repetition lemma collapses.

Also checked: no hoped-for counterexample exists in the data (rank-4 max run 10,
q5 rank-3 max compatible set 6), and no full-conjecture proof route was found.
I extracted the clean square-class characterization (V positive iff all nonzero
Plücker coordinates lie in one square class), which gives
|Gr^≥0| = (|Gr_{k,n}(F_q)| − #{mixed-sign Plücker points})/2, but this does not
yield log-concavity either.

**Verdict: pivot away from 365199. Audit documented; no claim, no credit.**

## Phase 2 — fresh MathDB screening

See screening.md (fetched via https://mathdb.com/api/posts/{id} and search API,
solution fields read first, actual primary sources read before work).
