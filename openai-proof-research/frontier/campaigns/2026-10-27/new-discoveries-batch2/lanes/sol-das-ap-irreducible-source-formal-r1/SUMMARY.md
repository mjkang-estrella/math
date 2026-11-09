# Literal Das Conjecture 5.1 refutation — formal component

Status: PROVED_LITERAL_N5_REFUTATION, not campaign acceptance. Published-source identity and novelty remain HOLD. Counts unchanged: 9 additional / 39 total / next 40; root alone accepts/counts. No manuscript.

`Das.literal_universal_bound_false` proves unconditionally:

```lean
¬ (∀ n : ℕ, 0 < n → ∀ A : Pattern n,
  ZeroDiagonal A → MinimalAP A → nonzeros A ≤ 2*n-2)
```

`Das.literal_conjecture51_false : ¬ Das.SourceConjecture` is the named-source version. `Das.literal_counterexample` supplies a literal order-five existential. The six plus/four minus witness is

```
0 + 0 0 +
+ 0 0 0 -
0 0 0 + 0
0 0 + 0 -
0 - + - 0
```

`Sign` is a three-constructor inductive type; `positive` is 1 on plus and 0 otherwise; `negative` is -1 on minus and 0 otherwise. `B A i j = positive A i j - negative A j i` is the actual signed formula. `B_support` proves support is plus at (i,j) or minus at (j,i); `B_overlap` proves overlap is 2. B is recomputed from `erase A i j` after every deletion.

`CutIrreducible` means every nonempty proper finite vertex set has an outgoing nonzero-support arc. `cut_iff_no_block` identifies this with absence of a nonempty partition whose outgoing rectangular block is zero. Grouping the indices in that set first is precisely the usual simultaneous row/column zero-block reducibility criterion. `cut_iff_strong` independently proves equivalence to reachability between every ordered pair in the actual support graph, with no finite connectivity certificate assumed. Reachability is reflexive/transitive edge closure; repeated vertices in a walk can be removed to obtain the customary graph path. Singleton and empty orders do not matter to the positive-order-five contradiction.

`APIrreducible` is exactly A irreducible, plus in each row, plus in each column, and B irreducible. `MinimalAP` uses exactly the source's every-single-nonzero-deletion definition, so no proper-subpattern monotonicity assumption is used or needed. `witness_AP`, `witness_deletions`, `witness_diagonal`, and `witness_count` are kernel-checked finite decisions, not imported Python propositions. The literal count is 10 and 10 > 2*5-2 = 8. `plus_obstructions` and `minus_obstructions` additionally check the specified six coverage obstructions and four outgoing zero blocks (zero-based indices in Lean). Initial A/B support contains the bidirected path 1–2–5–4–3; no support equality is assumed after deletion.

The endpoint negates the full all-orders assertion by one existential witness. No general-n family, optimality, smaller-order minimality, Conjecture 5.2, allowing algebraic positivity, or positive eigenvector claim is made.

## Source and chronology

Actual primary body: Sunil Das, *Sign patterns that allow algebraic positivity*, https://arxiv.org/abs/2112.00442v3 , PDF https://arxiv.org/pdf/2112.00442v3 . Submission history v3 22 March 2022; PDF title dated March 23. Journal reference LAA 653 (2022), 151–182. Frozen PDF SHA256 c7ebbffde1cd95c6cf363b9627d3dbd2311d066d0156fffd5a68e6df21198379. Actual p10 definitions, p22 Conjecture5.1, and surrounding Lemma3.10 proof and source digraph definition were read from the frozen extraction. The conjunction is not conditioned on allowing AP. Conjecture5.2 is separate. Lemma3.10 has an additional positive-component hypothesis violated by this witness. The frozen scout discovery Theorem1 and independent preliminary review/checker were read; no checker output is a Lean premise.

Published-source HOLD: final journal body was inaccessible in the inherited review. No claim that its numbered wording matches v3 is made. Novelty HOLD: inherited registry-head and historical-interval gaps, restricted thesis, incomplete citing literature, terminal Semantic Scholar 429, ScienceDirect denial, GitHub/raw/API/codeload/diff/patch denial and Google challenges remain parked. No request retried here and no browser/network request made. The readable author-preprint comparison and malformed ELA publisher-PDF failure from preliminary review are preserved in frozen evidence. No present worldwide-priority or registry-clearance claim.

## Validation and limits

All 71 actual owned mathematical declarations from Definitions and Witness, including private/generated helpers and derived Sign declarations, appear with fully elaborated types, origins, safety and transitive axiom reports in Audit.log. No filtering by public name or generated status. Allowed axioms only propext, Classical.choice, Quot.sound. Zero partial implementation declarations; zero unsafe declarations. Strict build uses warningAsError=true, autoImplicit=false, no sorry/admit/axiom/native_decide. Imports are pinned upstream dependencies, not new owned declarations.

RUN.md gives replay. `source-only.tar.gz` contains no owned compiled artifacts. Fresh extracted strict replay and its exhaustive audit are required and separately recorded under fresh-replay. `manifest.json` excludes itself and receipt.json; final verification is a separate guarded process after final writes. Administrative snapshots are never final-original equality targets; scientific frozen pairs are checked before/after. No shared, git, public, MathDB or other-lane writes.
