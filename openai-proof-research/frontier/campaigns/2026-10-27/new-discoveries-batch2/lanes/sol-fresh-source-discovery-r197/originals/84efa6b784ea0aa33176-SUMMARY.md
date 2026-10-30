# Literal factorial-product source endpoint

Complete formal refutation of Aivazidis–Loukaki–Müller, *On the common transversal probability*, J. Group Theory 27 (2024), 1233–1285, DOI 10.1515/jgth-2024-0030, published Problem 5.6, printed p.1281 (preprint Problem 12.6). This is a formal deliverable for root review; no manuscript, acceptance, or discovery credit is asserted.

The actual retained published question, not a catalogue paraphrase, was read at `inputs/source.txt` lines 2322–2332. It asks whether equality of products of f(x)=Γ(x+1)/x^x at distinct integers greater than one forces equal lengths and equal lists after rearrangement. There is no group-realization or equal-sum premise. Its full necessary statement is negated here.

Witnesses:

    A = {3,5,6,7,8,14,16,20,36}
    B = {4,10,12,15,18,21,32}

They are nonempty, disjoint, internally distinct, and every entry exceeds one. Their sizes are exactly nine and seven. Their rational products of t!/t^t are proved equal by `norm_num` after unfolding the transparent `qValue`; the kernel checks the arithmetic proof. No external arithmetic result or floating-point computation is a premise.

`f : ℝ → ℝ` is transparently defined as `Real.Gamma (x + 1) / x ^ x`, using real exponentiation. `gamma_dictionary` proves its equality at every natural t with the real cast of `qValue t` using the genuine `Real.Gamma_nat_eq_factorial` and `Real.rpow_natCast` theorems. The product dictionary is proved by list induction and rational-cast multiplicativity. Thus the literal Gamma endpoint is not an opaque renamed rational function and has no assumed dictionary bridge.

Key exact types in namespace `FactorialProduct` (with standard notation):

```lean
qValue : ℕ → ℚ
f : ℝ → ℝ
gamma_dictionary (t : ℕ) : f (t : ℝ) = (qValue t : ℝ)
rational_equality : (aList.map qValue).prod = (bList.map qValue).prod
literal_list_equality :
  (aList.map (fun (t : ℕ) => f (t : ℝ))).prod =
  (bList.map (fun (t : ℕ) => f (t : ℝ))).prod
literal_set_equality : (∏ t ∈ A, f (t : ℝ)) = ∏ t ∈ B, f (t : ℝ)
source_statement_negation : ¬ SourceStatement
integer_source_statement_negation : ¬ IntegerSourceStatement
finset_statement_negation : ¬ FinsetStatement
strong_distinct_statement_negation : ¬ StrongDistinctStatement
disjoint_nonempty_counterexample : ∃ S T : Finset ℕ,
  S.Nonempty ∧ T.Nonempty ∧ Disjoint S T ∧
  (∀ t ∈ S, 1 < t) ∧ (∀ t ∈ T, 1 < t) ∧ S.card = 9 ∧ T.card = 7 ∧
  (∏ t ∈ S, f (t : ℝ)) = ∏ t ∈ T, f (t : ℝ)
```

`SourceStatement` universally quantifies two natural lists, assumes their `Nodup`, entries >1 and literal real product equality, and concludes equal lengths AND `List.Perm`. `IntegerSourceStatement` is the same statement over ℤ, with real casts; its negation is proved directly by casting the explicit witness lists. These encode the source's integers literally. No signed-integer correspondence is left as an assumption. A finite list indexes the source's t₁,…,tₙ, and `Perm` expresses equality after rearrangement. `A` and `B` are the actual `toFinset` images; the equality between their products and the explicit list products is kernel-proved by simplification, and `list_conditions` proves `Nodup`. The Finset version therefore also matches the finite-set reading. `StrongDistinctStatement` adds nonemptiness and cross-disjointness, so the strongest plausible reading of distinctness is separately refuted. In each case nine ≠ seven already contradicts the length/cardinality conjunct. None of these negation theorems has residual hypotheses.

One mathematical module, `formal/FactorialProduct.lean`. `FullAudit.lean` uses `import all FactorialProduct`, inventories actual module-origin constants, and cross-checks against module metadata, including private equation lemmas and generated simp declarations. All 31 actual declarations have their types, origins, transitive axioms and safety flags recorded in the extracted `replay-receipt.json`; the full elaborated types also appear in `logs/FullAudit.log`. Only propext, Classical.choice and Quot.sound occur; every unsafe/partial/axiom flag is false. The audit tool is outside the mathematical module origins. No forbidden proof primitive is used.

`source-only.zip` and `manifest.json` form the deterministic source packet. Replay starts in a new extraction with zero own compiled artifacts, verifies original/copy hashes, Lean binary, Mathlib and all eight dependency revisions, dependency artifact hashes and the lockfile, compiles serially with warnings as errors, requires an empty mathematical compilelog, runs the exhaustive actual audit, and rechecks inputs and payload hashes. `archive-receipt.json` binds the archive and records two byte-identical builds. `replay-fresh/replay-receipt.json` is the fresh execution result; its own result, rather than this prose, determines replay success.

Strongest remaining objections are policy and bounded historical coverage, not an unproved finite bridge. Root adopted scoped substantive PASS and CLEAR_BOUNDED; the complete contrary counting proof is preserved verbatim in `inputs/preliminary-review.md`, and the full Candela–Helfgott comparison and access limits in `inputs/prior-review.md`. Smooth-restricted factorial valuations plus classical concentration and pigeonhole already give a complete alternative existence proof. Candela–Helfgott explicitly supplies the concentration-box mechanism, but its stated small 1-span theorem does not supply the factorial smooth restriction and two-scale estimates. Root may still judge that assembly routine under campaign policy. An earlier same-object collision or a previously published complete assembled theorem would defeat historical eligibility. The adjacent Jevtić vector-codebook body remains unread after 403. No global priority guarantee, new live literature screen, or credit follows from this certificate. No asymptotic theorem, minimality, or group realization is claimed.

See `PROVENANCE.md`, `FAILURES.md`, `frozen-before.json` and the replay's `frozen-after.json`. All work stayed in this lane; frozen sources were unchanged. No children, git commands, external messages, browser/account operations, posting, publishing, or uploads were performed.
