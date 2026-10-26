# Finite nonnegative Grassmannian: unaccepted research

Research date 2026-10-26. **No discovery credit, no Lean theorem, no resolution of the target conjecture.**

Source: John Machacek, *A finite totally nonnegative Grassmannian*, arXiv:2410.06177v2, revised October27,2025. The actual complete PDF/HTML definitions, Conjecture2.3, Theorems4.1/5.3/5.6 and Section6 examples were read. PDF SHA256157ff2538e6108cc90ccb11ce5a47056ce961f30d7637f95d63af795a8301cbb. Source URL https://arxiv.org/pdf/2410.06177v2 ; HTML https://arxiv.org/html/2410.06177v2 .

The exact Conjecture2.3 is **log-concavity** of the sequence of finite totally nonnegative Grassmannian cardinalities, for every finite field of odd characteristic. MathDB365199 calls it unimodality, but the source proposes the stronger log-concavity assertion. Positivity means being a square in the specified field. A point is a row space admitting a full-rank representative with all maximal minors square or zero. RREF normalizes a pivot minor to1, so all RREF maximal minors must themselves be square or zero. Do not use real positivity or positroid-variety point counts as a substitute. The source explicitly distinguishes these theories.

The live MathDB record was fetched in full: solutions, human_solves, model_attempts, comments, replies, formulations and attachments empty; progressnull. Snapshot in sources/365199-live.json. Absence of a posted solution is not proof of novelty.

## Exact exploratory enumerations

`run_words.py` recursively enumerates candidate compressed nonzero RREF column words over F3, imposing every ordered maximal-minor condition. The proposed completeness argument is below, not yet formalized/reviewed. Histograms by number of nonzero runs:

- rank2: L2:1, L3:2, L4:1.
- rank3: L3:1, L4:8, L5:17, L6:13, L7:3 (42 skeletons).
- rank4: L4:1, L5:22, L6:109, L7:214, L8:194, L9:80, L10:12 (632 skeletons).

For a skeleton with L nonzero runs, positive run lengths and arbitrary zero positions give the proposed count sum_(m=L)^n choose(n,m)choose(m−1,L−1), with generating function z^L/((1−z)(1−2z)^L). The rank3 candidate generating function simplifies to

    z^3(1+z−6z^2+3z^3)/(1−2z)^7.

The candidate rank3 values for n3..12 are1,15,120,703,3402,14448,55776,200160,677952,2190848. These agree with the source table and duality wherever covered.

`count_rref.c` is a separate complete finite enumeration for rank3, n3..12. It enumerates every pivot set and every RREF matrix allowed by the individual pivot minors, then directly tests every maximal3×3 determinant modulo3. It does not use the run skeletons, run bounds, generating function or their predictions. Its independent output in rref-counts.txt agrees with every candidate value above. This is exact integer arithmetic and finite computational evidence, not a formal all-n theorem or a novelty verdict.

Reproduce the C cross-check in this workspace (system g++/C development headers are absent; Lean's compiler links the standard library):

```sh
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanc -O3 -o count_rref count_rref.c
./count_rref > rref-counts.txt
```

The abandoned C++ version was not compiled. The C version declares its two standard-library functions directly to avoid missing system headers; integer counts here are safely below64bits. It is a cross-check, never an axiom or formal proof dependency.

## Proposed all-n classification argument to audit

Delete zero columns and compress adjacent equal nonzero columns; this preserves positivity because a maximal minor with repeated equal columns is zero, and every other minor has the same ordered determinant. In RREF the first new independent column is each successive standard basis vector. Before the third pivot, the first two rows form an F3-positive rank2 RREF word: append the future e3 pivot to any two earlier columns to read their2×2 minor. Its compressed skeleton is one of the four rank2 words.

After the third pivot, the pivot minors force each column to be (a,−b,c) with a,b,c∈{0,1}, nonzero. A compressed post-pivot word cannot return to a type v after a different type w. For if v,w are independent, one of the preceding standard basis vectors e_i makes det(e_i,v,w) nonzero; the ordered triples e_i,v,w and e_i,w,v would then have opposite signs, so one is negative in F3. If v,w are dependent, distinct nonzero types would be opposites, which the indicated orthant excludes. Thus the post-pivot compressed word has no repeated type. Enumerating all subsets/permutations of the seven post-pivot types, after each of the four prefixes, while checking all minors gives the42 skeletons. The rank4 exploration applies the same reasoning after the last pivot.

This argument and the exact42-skeleton enumeration need a rigorous formalization and independent review before any all-n count is claimed. In particular, the RREF/row-space uniqueness, compression/multiplicity bijection and finite-classification coverage must be proved, not assumed from small-n agreement.

## Negative findings and limits

The initial idea of contradicting log-concavity by a rank4 run of length11 did not work: this enumeration has maximum length10, so it does not supply the hoped-for asymptotic growth contradiction. The rank3 counts alone do not resolve the full source conjecture. A small exact hypergraph search over F5 rank3 projective directions containing a normalized basis found a largest compatible set of size6, again not the hoped-for contradiction; this observation is exploratory only.

Prior-art lead requiring an actual primary comparison: Jeremy Quail, *Ternary and quaternary positroids*, arXiv2403.06956v3. Its abstract characterizes ternary positroids as near-regular and describes sums of binary positroids/whirls. Do not infer either equality with the present finite-field-positive class or absence of an existing enumeration. A familiar/classically implied special case or a mere new interpretation of known counts earns no strict discovery credit.

Source-neighbor MathDB365198 concerns forests rather than Grassmannians. Its cited2410.06148 abstract proves an approximate Delta/2+18 theorem, while the MathDB statement has a sharper bound; exact source conjecture scope/parity has not been read, so no endpoint or parity counterexample is claimed.

No publication, posting, upload, author contact or external messages occurred. Research stays unaccepted until a substantive genuinely new result and every campaign gate are achieved.
