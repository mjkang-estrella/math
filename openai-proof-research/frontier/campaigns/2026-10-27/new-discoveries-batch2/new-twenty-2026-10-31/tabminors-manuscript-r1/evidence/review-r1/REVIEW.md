# Independent adversarial review: MathDB 359279 (tableau minors, conj:k+4)

Reviewer: Claude Opus 5.5, lane tabminors-review-r1, 2026-11-02/03 UTC. This is a review, not an acceptance. Credit is zero until root accepts.

Ground rules followed: no Lean, lake or leanchecker runs; no child agents; no git; no shared-ledger edits. Small pure-Python checks only, one process at a time, the largest at 314 MB peak and 20 s. All 212 read-only input files were hash-bound before and after the review, and they are unchanged (`inputs-sha256-before.txt`, `inputs-sha256-after.txt`).

## Verdicts

| Gate | Verdict |
|---|---|
| A. Source and MathDB fidelity | PASS |
| B. Ordinary mathematics | PASS |
| C. Lean evidence (read only) | PASS |
| D. Prior art | PASS, bounded; the JCTA body is unread |
| E. Significance | QUALIFIED_PASS |

No blocking objection. Five minor objections and one informational note are listed below.

## A. Fidelity

* **Source.** I read the source from the lane's e-print `main.tex`.
  * Tableaux are standard Young tableaux over [1, n] in English convention.
  * `T − m` deletes cell m, then repeatedly slides the smaller of the right and lower neighbours into the hole until the hole is an outer corner. It then subtracts 1 from every entry larger than m.
  * A k-minor is the result of k iterated deletions. mM_k is their multiset. The proof of `thm: exp lower bound` counts "n(n−1)⋯(n−k+1) minors in total", so the multiset ranges over deletion sequences.
  * A reading over subsets is not even well defined, because relabelling makes the result depend on the order of deletions.
* **Conjecture.** In the source, `conj:k+4` reads: k ≥ 1, T ∈ YT(n), n ≥ k + 4 ⇒ mM_k(T) determines T. The Lean `Conjecture` has exactly these quantifiers. MathDB 359279 restates the same statement.
* **Lean definitions.**
  * `IsSYT` is literal.
  * `slide` and `del` follow the source rule. The hole only ever reads the cells (i, j+1) and (i+1, j), so the stale value left behind is never read.
  * Fuel `size T` always suffices: each slide raises i + j by 1, and i + j ≤ n − 1.
  * `minors` sums over entries 1..size T.
* **Root's fix.** `diff` shows exactly seven changed lines in `fixed2/src/TabMinors.lean`. Each adds `noncomputable` to one of `slide`, `del`, `minors`, `den`, `ins`, `norm` and `step`. The fix is annotation-only. The control files are byte-identical to the lane's.

## B. Mathematics (independent Python, `scripts/`)

* **The counterexample.** `jdt.py` implements jeu de taquin deletion from the source text, with an SYT assertion on every output.
  * T₁ and T₂ are distinct SYT of size 12.
  * mM₈(T₁) = mM₈(T₂), with 19,958,400 minors each. The eight nonzero counts match the table in `proof.md`.
  * The multisets differ for every k = 1..7.
  * The source's figure (T − 8) is reproduced.
* **Lean certificate lists.** I parsed all sixteen Lean literals A1–A8 and B1–B8 as data. Each one equals my own level-by-level multiset exactly. So the certificate chain records the true jeu de taquin multisets, independently of Lean's `del`.
* **Exhaustive sweep over YT(n) for n ≤ 12.**
  * At n = k + 4, mM_k is injective for k = 1..7. It fails at k = 8 with 4 collision classes of 2 tableaux each: the two lane pairs and their transposes.
  * At n = k + 5, mM_k is injective for k = 1..7.
  * Both results agree with the lane and with the source's claim of verification for k ≤ 5.
* **Small claims from the source, all reproduced.**
  * mM₂ is injective at n = 6 and 7, but not at n = 5.
  * M₁ (sets) is injective at n = 5..8, but not at n = 4.
  * M₂ (sets) is injective at n = 8 and 9, but not at n = 7.
* **Hook argument.**
  * Lemma 1 holds for every word with N ≤ 9.
  * The Lemma 2 formula matches the exact dynamic program on 3,116 cases. Its proof is correct: Σ_σ 2^{rlmin(σ)} = (j+1)!, and C(k,j)(k−j)!(j+1)! = k!·min P.
  * The Theorem 3 pigeonhole is correct: 2^N hooks against polynomially many weight vectors.
  * The k = 11, n = 16 pair is confirmed: the two hooks are distinct and have equal mM₁₁.
  * An exhaustive formula search finds the first c = 4 hook collision at n = 12.
* **Not rechecked** (supplementary only): the C-sweep counts for k = 9..11, non-hook collisions first appearing at n = 13, and the absence of c = 6 hook collisions up to n = 26.

## C. Lean (read only)

* **Soundness lemmas.** `sum_ins`, `sum_norm`, `den_succ`, `minors_eq_den`, `chain` and `den_perm` are general lemmas, proved without any special assumptions.
* **The main chain.** `minors_eq` chains eight steps per tableau and closes with `den_perm 0 hAB`, where `hAB` is a permutation of explicit lists. `not_conjecture` applies the conjecture at k = 8, n = 12.
* **No vacuity.** `den 0 A8` is the literal weighted multiset.
* **Fuel exhaustion** is excluded in two ways: by the general argument in A, and by the `*_ok` certificates. Every `del` output survives in the merged lists, and each is checked to be an SYT of size exactly one less.
* **Root's fixed2 logs.**
  * Builds are strict (`-DwarningAsError=true`), and leanchecker passes on all three modules.
  * `not_conjecture` depends only on propext, Classical.choice and Quot.sound.
  * AuditFull covers all 140 constants in module TabMinors, generated ones included. None is unsafe or partial, none lacks a body, and no other axioms appear.
  * Both negative controls are rejected, as intended.
* **Audit discrepancy.** The lane's own 137-declaration audit missed the `_unsafe_rec` companions. The fixed2 packet is the one to accept.

## D. Prior art

* **arXiv.** The live abs page for 2307.13161 shows only v1 (24 Jul 2023).
* **Journal version (the lane missed it).** J. Combin. Theory Ser. A 209 (2025) 105950, doi 10.1016/j.jcta.2024.105950, online 2024-08-26 (OpenAlex). The body is unread, because ScienceDirect returns 403 and that route is excluded. An unverified search snippet places the multiset conjecture there as Conjecture 7.2.
* **Later talks still pose the conjecture.** Herden's Rutgers slides of 27 Feb 2025, which postdate the journal version, still present n ≥ k + 4 as a conjecture (slides 22–23).
* **Follow-ups.** OpenAlex lists 0 works citing the JCTA paper. Topical searches from 2023 to 2026 found no refutation (`receipts/`).
* **Related work.** Jiradilok, arXiv 1610.05354, studies the partition analogue: reconstructing partitions from multisets of their k-minors, with n − G(n) = O(n/log n). It is a different object and implies nothing about tableaux, but it should be cited next to Theorem 3.
* **Registries**, checked via `/commits/HEAD` only:
  * openai/math is still at 4eaee875 (2026-10-30T00:35:35Z).
  * Omega has advanced to ab2e0d0 (2026-11-02T23:54:07Z). Its HEAD commit touches a single unrelated file. The intermediate delta was not screened.

## E. Significance: QUALIFIED_PASS

**For:**

* It is a literal refutation of a published conjecture (JCTA, and restated in 2025 talks), under the source's own conventions.
* It is not an endpoint or convention artefact:
  * the failure recurs at n = k + 5;
  * the hook weight formula plus pigeonhole shows that no bound n ≥ k + c works for any constant c. That refutes the proposed linear-plus-constant shape itself.
* Nothing in the source's own data reveals it (they checked k ≤ 5, and injectivity at n = k + 4 actually persists through k = 7).
* The set version, sibling 359278, is silent on multisets.
* No source lemma yields the result, so it is not a bridge or corollary.
* The general-c mechanism needs the new hook structure, because naive counting over all SYT does not pigeonhole.

**Qualifications:**

* The Lean endpoint covers only the literal k = 8 refutation. Theorem 3 is an ordinary proof only.
* The JCTA body is unread.
* The core certificate is a computer-found counterexample just beyond the authors' verified range.

## Objections

1. *Minor.* `proof.md` §2 says "4 colliding rows out of 140,152 tableaux". The correct count is 4 colliding pairs, i.e. 8 tableaux.
2. *Minor.* The journal version (JCTA 209, 105950) must be cited, and the paper must state that the conjecture is quoted from arXiv v1 and that the journal body was not read.
3. *Minor.* Acceptance must bind the fixed2 `TabMinors.lean` (sha 66fee9a4…) and its 140-declaration audit, not the lane's sha 88bb9504… and 137-declaration audit.
4. *Minor.* Theorem 3 must not be presented as Lean-verified. Cite Jiradilok 1610.05354 alongside it.
5. *Minor.* The Omega delta 0561ac6..ab2e0d0 was not screened.
6. *Info.* Some supplementary sweep claims were not rechecked (listed under B).

## Recommendation and next actions

The mathematics, fidelity and Lean evidence are sound, and significance is QUALIFIED_PASS. I recommend root proceed to its acceptance decision once the wording and citation fixes above are in the paper.

Optional follow-ups:

* a path screen of the Omega delta;
* a lawful non-ScienceDirect read of the JCTA text.

## Files

* `review.json`: structured verdicts.
* `scripts/jdt.py`, `check_pair.py`, `sweep.py`, `hooks.py`: the independent checks.
* `logs/`: check_pair.json, sweep10/12.json, hooks.json, plus timing files.
* `receipts/`: dated HTTP receipts and search receipts.
* `downloads/`: untrusted fetched data, each source in its own directory.
* `inputs-sha256-before.txt` and `inputs-sha256-after.txt`: input hash bindings.
