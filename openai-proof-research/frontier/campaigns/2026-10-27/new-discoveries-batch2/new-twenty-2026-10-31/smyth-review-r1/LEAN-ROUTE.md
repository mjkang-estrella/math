# Lean route plan for the 332037 refutation (Gate C)

I reviewed this by reading only. I did not run Lean, lake or leanchecker in this lane. Every remark about whether something compiles is a prediction for Sol to confirm on the pinned toolchain.

## 1. Cheapest literal endpoint

```lean
def U (m n : ℕ) : Set (Fin m → ℕ) := {f | ∑ i, f i = n}
def rearr {m} (f : Fin m → ℕ) : List ℕ := (List.ofFn f).insertionSort (fun x y => y ≤ x)
def DomL (l₁ l₂ : List ℕ) : Prop := l₁.sum = l₂.sum ∧ ∀ j, (l₂.take j).sum ≤ (l₁.take j).sum
def Dom {m} (f g : Fin m → ℕ) : Prop := DomL (rearr f) (rearr g)      -- f ⊵ g
def Conjecture15 : Prop :=
  ∀ A a B b : ℕ, B ≤ A → b ≤ a →
    ∃ γ : (U A b × U B a) → (U A a × U B b), Function.Injective γ ∧
      ∀ x, Dom (Fin.append x.1.1 x.2.1) (Fin.append (γ x).1.1 (γ x).2.1)
theorem not_conjecture15 : ¬ Conjecture15
```

This matches the source (TeX lines 24–28, 73–79) as follows:

* **Natural numbers.** ℕ is the right domain, because the source requires A ≥ B ≥ 0 and a ≥ b ≥ 0.
* **Compositions.** `Fin m → ℕ` is the source's λ : [m] → ℕ, so `U m n` is exactly U^m_n.
* **Concatenation.** `Fin.append` is (λμ)(i) = λ(i) for i ≤ A and μ(i − A) after that.
* **Rearrangement.** `rearr` is the non-increasing rearrangement.
* **Dominance.** `DomL` is the source's partition dominance. It includes the sum condition |λ| = |μ| and every partial sum. `take j` past the end of the list gives the full sum, which is the same as padding with zeros.
* **Orientation.** `Dom (source) (image)` is λ1μ1 ⊵ λ2μ2, which is the source's orientation.
* **Domain and codomain.** The domain is U^A_b × U^B_a and the codomain is U^A_a × U^B_b, in the source's order.

Optional fidelity lemmas (cheap, and recommended for the statement-fidelity review):

* `List.sorted_insertionSort` shows `(rearr f).Sorted (· ≥ ·)`.
* `List.perm_insertionSort` shows `rearr f ~ List.ofFn f`.

Together these show `rearr` really is the non-increasing rearrangement. A further sanity lemma would be useful: `DomL` is reflexive and transitive, and on sorted lists of equal length it agrees with the source's "∀ j ≥ 1" form.

## 2. Decidable certificate and kernel cost

* **The only kernel evaluations.** `SL.length = 1137` and `TL.length = 1134`. These are filters over the structural enumerator `comps` (4410 and 4620 pairs). Each pair needs one 5-element insertion sort and at most 8 × 6 prefix-sum comparisons. That is roughly 9030 × (10 + 8·6·5) ≈ 2–3 million Nat operations on literals, which the kernel's GMP-accelerated `Nat.ble`, `Nat.add` and `Nat.decEq` handle.
* **Use `decide +kernel`, not plain `decide`.** Use `decide +kernel`, or `decide!` on older toolchains (it adds no axiom, unlike `native_decide` / `+native`). Plain `decide` first tries the elaborator's `whnf` on the instance. Over a 4410-element list it is likely to time out or hit `maxRecDepth`. The fallback is to split the count into blocks, for example by the first part of λ (0..19), with one `decide +kernel` per block, and to sum the blocks.
* **Expected cost.** Seconds to a few minutes of kernel time. This is far below the per-file budgets of earlier accepted certificates.
* **Closure property.** No kernel enumeration is needed for closure. It follows from `DomL.trans` plus `domB_iff` (the Boolean prefix test is exact for length-5 lists).

## 3. Reading the UNCOMPILED draft `expanded-corpus-r151/candidate-332037/Smyth1512Refutation.lean` (sha256 fe44f076…)

### What is right

* **Definitions (lines 31–57).** The definitions are literal and faithful, as described in §1. The orientation in `Conjecture15` (line 57) is correct: `Dom (concat source) (concat image)`. The quantifier order and the domain and codomain are correct.
* **Proof architecture (lines 186–241).** The architecture is the right one:
  1. specialise to (3, 20, 2, 19);
  2. pull γ back to lists;
  3. show that ψ maps `SL.toFinset` into `TL.toFinset`, using `inDB_mono` (transitivity);
  4. ψ is injective on `SL`;
  5. `Finset.card_le_card_of_injOn` gives 1137 ≤ 1134, a contradiction.
* **Certificate data (lines 61–63).** The 8 generators match my independent recomputation (`logs/cert.log`). They are pairwise incomparable, and each one is itself realised as a type in X.
* **Enumerator and nodup lemmas (lines 91–132).** `mem_comps` and `nodup_comps` follow standard patterns.
* **Small lemmas.** `DomL.trans` (lines 136–137) is correct as written. `psum_of_ge` is correct.

### Likely compile defects (to be confirmed by Sol)

1. **Lines 85–86: plain `by decide` on 4410 and 4620 element filters.** This will very likely be too slow or hit `maxRecDepth` in the elaborator. Replace it with `by decide +kernel`, or split it into blocks as described in §2.
2. **Line 151: `rw [psum_of_ge (by omega), psum_of_ge (by omega)]`.** The `by omega` side goals are elaborated before the implicit list `l` is unified, so omega sees metavariables. Use `psum_of_ge (l := l) (by omega)` and `psum_of_ge (l := g) (by omega)`. The goal after rewriting is `l.sum ≤ g.sum`. `hs ▸ le_rfl` with `hs : g.sum = l.sum` may need `hs.symm ▸ le_rfl` or `le_of_eq hs.symm`.
3. **Line 237: `rw [← Classical.choose_spec (real p hp.1), ← Classical.choose_spec (real q hq.1), this]`.** Rewriting `p` right to left also rewrites the `p` that occurs inside `real p hp.1`, so this is likely to fail with "motive is not type correct". Replace it with an explicit chain: `calc p = toL xp := (choose_spec _).symm`, then `_ = toL xq := by rw [this]`, then `_ = q := choose_spec _`.
4. **Line 238: `Finset.card_le_card_of_injOn`.** In current Mathlib the second argument is `Set.MapsTo ψ s t`, which is definitionally `∀ ⦃a⦄, a ∈ s → ψ a ∈ t`. The draft's `maps` has the shape `∀ p ∈ s, …`, so it may need `fun p hp => maps p hp`.
5. **Line 78: the `×ˢ` instance on `List`.** This needs Mathlib's `List.product` `SProd` instance. If it is not available, use `List.product`, or `(comps 3 19).flatMap (fun l => (comps 2 20).map (l, ·))`. `SL_nodup` (line 132) uses `List.Nodup.product` and must match the same choice.
6. **Line 190: `let toL : ∀ {A a B b : ℕ}, …`.** This is a let-bound function with implicit binders inside a tactic proof. It usually works, but `simp only [toL]` and the defeq steps at lines 224 and 231 depend on zeta-delta. A top-level `def toL` is more robust.
7. **Lemma names to check on the pinned Mathlib.** `List.ofFn_fin_append`, `List.sum_ofFn`, `List.ofFn_injective`, `List.getD_eq_getElem`, `List.length_insertionSort`, `List.toFinset_card_of_nodup`, `List.toFinset_card_le`, `List.nodup_flatMap`, `List.Pairwise.imp_of_mem`.

### Mathematical gaps

* None. The argument is complete: injectivity plus dominance-monotone membership in a down-set gives an injection from S into T, and |S| > |T|.
* The draft never needs sortedness of `rearr` in the proof. That is fine for the refutation. Sortedness matters only for the fidelity of the statement, and `insertionSort` with `y ≤ x`, a total preorder, provides it. Adding the lemmas from §1 is recommended.

## 4. Endpoint-shape cautions for the fidelity reviewer

* Do not replace `U` with `Finset` or with lists in the **statement**. Lists are used only inside the proof.
* Do not weaken `Dom` to a test on the first 5 prefixes in the **statement**. `domB` is a proof device, connected to `DomL` by `domB_iff`.
* The statement must quantify over all four naturals with `B ≤ A → b ≤ a`. Proving only the specialised `¬ ∃ γ …` at (3, 20, 2, 19) is a stronger intermediate, but the endpoint should be `¬ Conjecture15`.
