# Independent review: MathDB 356369 / Rust's game-sequence identity

Decision: **PASS: complete source-level verification of the known counterexample at n=20.** Reviewed on 2026-10-26 by the independent discrete/Fibonacci lane. The reviewer did not author the Rust artifact and made no edits to its source, paper, metadata, or git state.

The reviewed authoritative package is `thirty-proof-campaign/outcomes/rust/`, after the parent's final-ready declaration and the minor paper precision correction described below.

## Exact final files reviewed

- `formal/Rust.lean`: SHA256 `9e7986a9c1f3a9f74c1a6c4b05b6d93b8850a300498476b1de60edb1b113f037`.
- Final `main.tex`: SHA256 `417ceeb66f2770243579511407aac3153a60b2bd99a47a5a71e48ec355e9c2d9`.
- Main theorem: `RustCounterexample.rust_counterexample`.

The integrated Lean file is byte-identical to `extension-rust/formal/Rust.lean`. The complete paper was read, and the final paper-only wording change was reread and hashed. Authored-PDF rendering and visual QA are the parent's separate step; this review makes no layout certification.

## Fresh pinned audit

Copied the exact final Lean file and manifest into the unique scratch outcome `extension-discrete-second/review-rust/`, then ran `twenty-proof-campaign/verify_outcome.py` independently there.

Result: **PASS**, Lean 4.34.1, **35 declarations**, warning-as-error compilation of both source and all-declaration audit, with pinned dependency revisions checked by the verifier. The only observed foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The scratch `build/audit.json` and logs bind the exact Lean hash above. No proof placeholders, extra postulates, external automaton correctness hypotheses, or prohibited evaluation mechanism occur.

## Actual source and prior attribution

Read the actual archived Shallit primary source, *Some Tribonacci Conjectures*, arXiv:2210.03996v1, particularly:

- Section 3, Definition 1 and Table 2: initial values and the game-sequence greedy rule;
- Section 3.2: the seven admissibility conditions and the two separate minimality conditions;
- Section 4, Conjecture 5 and its disproof: Rust's exact identity and the existing witness n=20.

Definition 1 fixes `(X(0),Y(0))=(0,0)` and `(X(1),Y(1))=(1,2)`, then chooses positive unused x<y whose difference has not appeared among previous sums or differences. Its wording about the least pair is resolved by Section 3.2: x is minimal among all admissible pairs, then y is minimal for that x. Thus the formal lexicographic order is explicitly the source order, not a new interpretation. The Section 3.2 Walnut code itself includes history index zero, while the prose lists positive indices; positivity makes this difference harmless, and the formal bridge now proves that fact.

Shallit's 2022 source already identifies n=20 and proves the stronger existence of infinitely many counterexamples using Walnut. The current paper explicitly credits that known result and limits its formal claim to the single n=20 refutation. It does not claim a new disproof, first formalization, or an infinite-counterexample theorem. MathDB 356369 itself records the conjecture as refuted. The two primary snapshot hashes recomputed exactly as recorded in `primary-reference.json`:

- `source.html`: `655104ea8abcf3068be0adc563ee88bec111049fa3441560de1751f623b19269`.
- `source.txt`: `6964fa2f7e9f150eee89fe8b35abcd1e9c525634908b10feb3b170c6b482f323`.

## Complete infinite construction, not an isolated prefix

The module constructs total functions `state`, `pair`, `X`, and `Y` on all natural indices by recursion. Each state consists of finite used-value and blocked-difference sets. There is no finite table substituted for the source sequences.

`holes` searches through zero up to one past the finite set's maximum. `holes_nonempty` proves that the latter value is missing. `mex_not_mem`, `mex_le`, and `mem_of_lt_mex` establish the full least-excluded property, including competitors beyond the finite search range. Thus the search bound does not assume or artificially restrict the existence of future source pairs.

Given used values U and blocked differences D, the next pair is defined by

`x=mex(U)`, `d=mex(D ∪ {u−x : u∈U})`, `y=x+d`,

with natural-number truncated subtraction. Because zero belongs to both forbidden sets, x and d are positive. A previous u<x contributes only zero, already excluded; this truncation cannot incorrectly eliminate a positive admissible difference.

`nextPair_least` proves the entire source selection condition for arbitrary finite U,D containing zero. It establishes x>0, y>x, unused x and y, and unused y−x. For any competing admissible (u,v), mex minimality gives x≤u. If u=x, then v−x is outside the whole excluded difference set: if some earlier w satisfied w−x=v−x>0, natural arithmetic forces w=v, contrary to v being unused. Thus d≤v−x and y≤v. This covers every possible source candidate, without a bounded-candidate assumption or an assumed greedy bridge.

## Exact history and original-definition bridges

`state_successor` and `state_history` identify the actual recursive state with the histories of both constructed functions: all earlier X/Y values, and all earlier differences/sums. The update includes both newly chosen values and both new difference/sum values; no source exclusion is omitted.

The final file contains explicit original-definition rewriting lemmas:

- `range_with_origin` identifies the inclusive range with zero inserted into the positive-index interval;
- `histories_with_origin` proves the corresponding used/difference history identities;
- `admissible_insert_origin` proves that adding zero changes no admissible pair, using positivity of x,y,y−x;
- `leastPair_insert_origin` transfers the full least-pair condition, including all competitors;
- `original_definition_bridge` supplies all four source seeds and the exact positive-history greedy condition at every subsequent index.

Its formal index `n≥1` for the next pair n+1 is exactly the source's selection range at indices greater than one. This resolves the initial review precision concern that histories including zero should not simply be called identical to positive-index histories without proof.

`leastPair_unique` proves uniqueness of a least pair by comparing its two coordinates in order. `source_rule_unique` then uses strong induction: coordinate equality at every earlier index makes both histories equal, and least-pair uniqueness determines the next pair. This establishes global uniqueness of the sequence satisfying the formal source selection rule. Combined with the proven seed/positive-history bridge, the construction is the source's actual recursive sequence, rather than one convenient finite realization.

## Exact counterexample and paper consistency

`initial_values` proves the four seeds. `exact_values` uses ordinary kernel-checked `decide` on the total recursive definitions to prove

`X(20)=30`, `Y(20)=56`, `X(56)=86`, `Y(30)=84`.

The main theorem combines source-rule validity, seeds, the admissible index 20≥1, and failure of Rust's exact proposed equality. Substitution gives left side 86+84=170 and right side 2·30+2·56−1=171. Natural subtraction does not introduce an issue: the certified right side is positive and agrees with ordinary integer arithmetic. One concrete admissible counterexample completely refutes the source's universal equality.

For an independent narrative check, the reviewer replayed Definition 1 directly with a simple positive-integer scan, separately from the mex implementation. It matches the source's entire printed Table 2 prefix, all four witness entries, and all 56 pairs printed in the paper. This auxiliary replay is a review cross-check, not a substitute for the Lean proof. Its script and output are in the unique scratch review directory.

The initial paper wording could be read as claiming a separate Lean theorem certifying every printed table entry. The formal file asserts the four needed witness entries (and seeds), while the larger table is explanatory. The reviewer requested a precision change. The final paper now says exactly that the four required witness entries are checked in Lean's kernel. Its updated hash above includes that correction. All 56 displayed pairs were independently checked and are correct.

## Final assessment and limits

**PASS at the exact final Lean/TeX hashes above.** The source's full greedy reading, infinite total construction, state histories, original seed/index convention, least-pair minimality, and global uniqueness are covered. The counterexample is computed from these actual functions with no imported automaton or assumed values.

Describe the outcome as verification of **Shallit's published n=20 counterexample to Rust's identity**. It is a substantive full refutation of the given universal identity, but it is not a new mathematical disproof and does not formalize the stronger infinite-counterexample assertion. No unresolved mathematical, source-fidelity, formal-coverage, or attribution objection remains.


## Parent production addendum

After the independent mathematical review, one concluding sentence giving the same two unequal integers was shortened to keep the proof-ending word and QED on page2. No formula, hypothesis, assertion or Lean source changed. Final main.tex SHA256 is `fab518913fa8853787e87f14b2dd3a77b964b4e6c33e5ec40d1004c68e46f238`. All3 final rendered pages were individually inspected; proof conclusion is together and no overflow or unresolved references remain. The independently reviewed mathematical content is unchanged.
