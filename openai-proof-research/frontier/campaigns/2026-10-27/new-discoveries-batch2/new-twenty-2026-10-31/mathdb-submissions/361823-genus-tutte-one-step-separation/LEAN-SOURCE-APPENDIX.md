# Lean source appendix (MathDB 361823)

All 13 modules of `src/`, in import order, byte-identical to the files.

### `GTDefs.lean`

```lean
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# The genus-g Tutte polynomial (Miezaki–Oura–Sakuma–Shinohara, Definition 1.3)

Source: T. Miezaki, M. Oura, T. Sakuma, H. Shinohara, *The Tutte polynomials of genus g*,
arXiv:2402.06845v1, Definition 1.3 (p. 4) and Conjecture 5.12 (p. 27).

For a matroid `M` on `E` with rank function `ρ` and a `g`-tuple `(A₁,…,A_g)` of subsets of `E`, put
`Λ₁ = {1,…,g}`, `Λ₂ = binom(Λ₁,2)`, `A∩(λ) = ⋂_{i∈λ} A_i`, `A∪(λ) = ⋃_{i∈λ} A_i`, and

`T^(g)(M) = Σ_{A₁,…,A_g ⊆ E} Π_{λ∈Λ₁} (x_λ-1)^{ρ(E)-ρ(A_λ)} (y_λ-1)^{|A_λ|-ρ(A_λ)}`
`            × Π_{λ∈Λ₂} (x∩(λ)-1)^{ρ(E)-ρ(A∩(λ))} (y∩(λ)-1)^{|A∩(λ)|-ρ(A∩(λ))}`
`            × Π_{λ∈Λ₂} (x∪(λ)-1)^{ρ(E)-ρ(A∪(λ))} (y∪(λ)-1)^{|A∪(λ)|-ρ(A∪(λ))}`.

Every slot `λ ∈ Λ₁`, `∩(λ)`, `∪(λ)` (`λ ∈ Λ₂`) carries its own pair of variables. We index the slots by
`Slot h = Fin h ⊕ ({p : Fin h × Fin h // p.1 < p.2} × Bool)`: `inl i` is the singleton slot `i`,
`inr (p, false)` is `∩(p)` and `inr (p, true)` is `∪(p)`. The variable `(s, false)` is `x_s` and `(s, true)`
is `y_s`. The rank is Mathlib's matroid rank `Matroid.eRk`, read in `ℕ` (`ENat.toNat`); on a finite
ground set it is finite, so nothing is lost.
-/

open MvPolynomial Finset

namespace GenusTutte

/-- `if_pos`/`if_neg` (deprecated names in this toolchain). -/
theorem if_pos' {c : Prop} [Decidable c] (hc : c) {β : Sort*} (a b : β) :
    (if c then a else b) = a := by simp [hc]

theorem if_neg' {c : Prop} [Decidable c] (hc : ¬ c) {β : Sort*} (a b : β) :
    (if c then a else b) = b := by simp [hc]

/-- Slots of the genus-`h` Tutte polynomial. -/
abbrev Slot (h : ℕ) := Fin h ⊕ ({p : Fin h × Fin h // p.1 < p.2} × Bool)

/-- The set `A_λ`, `A∩(λ)` or `A∪(λ)` attached to a slot. -/
def slotSet {α : Type*} [DecidableEq α] {h : ℕ} (A : Fin h → Finset α) : Slot h → Finset α
  | Sum.inl i => A i
  | Sum.inr (p, false) => A p.1.1 ∩ A p.1.2
  | Sum.inr (p, true) => A p.1.1 ∪ A p.1.2

/-- **The genus-`h` Tutte polynomial** of a matroid on a finite type whose ground set is everything
(the review's endpoint definition, literally). -/
noncomputable def genusTutte (h : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (_hE : M.E = Set.univ) : MvPolynomial (Slot h × Bool) ℤ :=
  ∑ A : Fin h → Finset α, ∏ s : Slot h,
    (X (s, false) - 1) ^ ((M.eRk Set.univ).toNat - (M.eRk (slotSet A s : Set α)).toNat) *
    (X (s, true) - 1) ^ ((slotSet A s).card - (M.eRk (slotSet A s : Set α)).toNat)

/-- MathDB 361823 (Conjecture 5.12 of the source, for a given positive integer `g`). -/
def MiezakiConj512 (g : ℕ) : Prop :=
  ∃ (n : ℕ → ℕ) (M N : ∀ i, Matroid (Fin (n i))) (hM : ∀ i, (M i).E = Set.univ)
    (hN : ∀ i, (N i).E = Set.univ),
    StrictMono n ∧ ∀ i, genusTutte g (M i) (hM i) = genusTutte g (N i) (hN i) ∧
      genusTutte (g + 1) (M i) (hM i) ≠ genusTutte (g + 1) (N i) (hN i)

/-! ## An abstract version: any "rank" function on finsets -/

/-- One summand, for an arbitrary function `ρ` in place of the rank and `R` in place of `ρ(E)`. -/
noncomputable def term (h : ℕ) {γ : Type*} [DecidableEq γ] (ρ : Finset γ → ℕ) (R : ℕ)
    (A : Fin h → Finset γ) : MvPolynomial (Slot h × Bool) ℤ :=
  ∏ s : Slot h, (X (s, false) - 1) ^ (R - ρ (slotSet A s)) *
    (X (s, true) - 1) ^ ((slotSet A s).card - ρ (slotSet A s))

/-- The genus-`h` polynomial of an abstract rank function. -/
noncomputable def gt (h : ℕ) {γ : Type*} [Fintype γ] [DecidableEq γ] (ρ : Finset γ → ℕ) (R : ℕ) :
    MvPolynomial (Slot h × Bool) ℤ :=
  ∑ A : Fin h → Finset γ, term h ρ R A

theorem genusTutte_eq_gt (h : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) :
    genusTutte h M hE = gt h (fun B : Finset α => (M.eRk (B : Set α)).toNat) (M.eRk Set.univ).toNat := rfl

/-- Summands agree when every slot has the same size and the same `ρ`-value. -/
theorem term_congr (h : ℕ) {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] (ρ : Finset γ → ℕ)
    (ρ' : Finset δ → ℕ) (R : ℕ) (A : Fin h → Finset γ) (A' : Fin h → Finset δ)
    (hc : ∀ s, (slotSet A' s).card = (slotSet A s).card)
    (hr : ∀ s, ρ' (slotSet A' s) = ρ (slotSet A s)) :
    term h ρ' R A' = term h ρ R A := by
  unfold term
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hc s, hr s]

/-! ## Slot semantics: every slot is an intersection or a union over its inputs -/

/-- The input indices of a slot. -/
def slotIn {h : ℕ} : Slot h → Finset (Fin h)
  | Sum.inl i => {i}
  | Sum.inr (p, _) => {p.1.1, p.1.2}

/-- Whether a slot is read as an intersection (singletons count as intersections). -/
def slotCap {h : ℕ} : Slot h → Bool
  | Sum.inl _ => true
  | Sum.inr (_, b) => !b

theorem mem_slotSet_cap {α : Type*} [DecidableEq α] {h : ℕ} (A : Fin h → Finset α) (s : Slot h)
    (hs : slotCap s = true) (x : α) : x ∈ slotSet A s ↔ ∀ i ∈ slotIn s, x ∈ A i := by
  rcases s with i | ⟨p, b⟩
  · simp [slotSet, slotIn]
  · cases b
    · simp [slotSet, slotIn]
    · simp [slotCap] at hs

theorem mem_slotSet_cup {α : Type*} [DecidableEq α] {h : ℕ} (A : Fin h → Finset α) (s : Slot h)
    (hs : slotCap s = false) (x : α) : x ∈ slotSet A s ↔ ∃ i ∈ slotIn s, x ∈ A i := by
  rcases s with i | ⟨p, b⟩
  · simp [slotCap] at hs
  · cases b
    · simp [slotCap] at hs
    · simp [slotSet, slotIn]

theorem slotIn_nonempty {h : ℕ} (s : Slot h) : (slotIn s).Nonempty := by
  rcases s with i | ⟨p, b⟩ <;> simp [slotIn]

theorem slotIn_card_le {h : ℕ} (s : Slot h) : (slotIn s).card ≤ 2 := by
  rcases s with i | ⟨p, b⟩
  · simp [slotIn]
  · exact Finset.card_le_two

theorem eq_inl_of_slotIn_card {h : ℕ} (s : Slot h) (hs : (slotIn s).card ≤ 1) :
    ∃ i, s = Sum.inl i ∧ slotIn s = {i} := by
  rcases s with i | ⟨p, b⟩
  · exact ⟨i, rfl, rfl⟩
  · exfalso
    have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    simp [slotIn, Finset.card_pair hne] at hs

/-- Slot sets commute with mapping all probes along an embedding. -/
theorem slotSet_map {α β : Type*} [DecidableEq α] [DecidableEq β] {h : ℕ} (e : α ↪ β)
    (A : Fin h → Finset α) (s : Slot h) :
    slotSet (fun i => (A i).map e) s = (slotSet A s).map e := by
  rcases s with i | ⟨p, b⟩
  · rfl
  · cases b
    · simp [slotSet, Finset.map_inter]
    · simp [slotSet, Finset.map_union]

end GenusTutte
```

### `GTSparse.lean`

```lean
import GTDefs
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Sparse paving matroids with loops, and their rank function

Data: a finite type `γ`, a set `N` of non-loops, a rank `r ≥ 1` and a family `H` of `r`-subsets of `N`
whose distinct members meet in at most `r - 2` elements (the "circuit-hyperplanes").
A finset `I` is independent iff `I ⊆ N`, `|I| ≤ r` and `I ∉ H` (PROOF-361823 §1, with loops added).
We build this as a genuine Mathlib `Matroid` (`IndepMatroid.ofFinset`) and prove the rank formula
`rk(S) = min(r, |S ∩ N|) - [S ∩ N ∈ H]`.
-/

open Finset

namespace GenusTutte

/-- Sparse paving data with loops. -/
structure SP (γ : Type*) [DecidableEq γ] where
  N : Finset γ
  r : ℕ
  H : Finset (Finset γ)
  hr : 1 ≤ r
  hsub : ∀ B ∈ H, B ⊆ N
  hcard : ∀ B ∈ H, B.card = r
  hinter : ∀ B ∈ H, ∀ B' ∈ H, B ≠ B' → (B ∩ B').card + 2 ≤ r

namespace SP

variable {γ : Type*} [DecidableEq γ] (S : SP γ)

/-- Independence on finsets. -/
def Ind (I : Finset γ) : Prop := I ⊆ S.N ∧ I.card ≤ S.r ∧ I ∉ S.H

theorem ind_empty : S.Ind ∅ := by
  refine ⟨empty_subset _, Nat.zero_le _, fun h => ?_⟩
  have := S.hcard _ h
  have := S.hr
  simp at *
  omega

theorem ind_subset {I J : Finset γ} (hJ : S.Ind J) (hIJ : I ⊆ J) : S.Ind I := by
  obtain ⟨hJN, hJr, hJH⟩ := hJ
  refine ⟨hIJ.trans hJN, (card_le_card hIJ).trans hJr, fun hI => hJH ?_⟩
  have hc := S.hcard I hI
  have : I = J := eq_of_subset_of_card_le hIJ (by omega)
  rwa [← this]

theorem ind_aug {I J : Finset γ} (hI : S.Ind I) (hJ : S.Ind J) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ S.Ind (insert e I) := by
  obtain ⟨hIN, hIr, hIH⟩ := hI
  obtain ⟨hJN, hJr, hJH⟩ := hJ
  obtain ⟨e, heJ, heI⟩ : ∃ e ∈ J, e ∉ I := by
    by_contra hcon
    push Not at hcon
    exact absurd (card_le_card hcon) (by omega)
  have hbase : ∀ f ∈ J, f ∉ I → insert f I ⊆ S.N ∧ (insert f I).card ≤ S.r := fun f hf hfI =>
    ⟨insert_subset (hJN hf) hIN, by rw [card_insert_of_notMem hfI]; omega⟩
  by_cases he : insert e I ∈ S.H
  · -- then `J ⊄ insert e I`, giving a second candidate `f`
    have hc := S.hcard _ he
    rw [card_insert_of_notMem heI] at hc
    obtain ⟨f, hfJ, hf⟩ : ∃ f ∈ J, f ∉ insert e I := by
      by_contra hcon
      push Not at hcon
      have hsub : J ⊆ insert e I := hcon
      have : J = insert e I :=
        eq_of_subset_of_card_le hsub (by rw [card_insert_of_notMem heI]; omega)
      exact hJH (this ▸ he)
    rw [mem_insert, not_or] at hf
    refine ⟨f, hfJ, hf.2, (hbase f hfJ hf.2).1, (hbase f hfJ hf.2).2, fun hf' => ?_⟩
    have hne : insert e I ≠ insert f I := by
      intro hEq
      have : f ∈ insert e I := hEq ▸ mem_insert_self f I
      rw [mem_insert] at this
      rcases this with h | h
      · exact hf.1 h
      · exact hf.2 h
    have hint := S.hinter _ he _ hf' hne
    have : I ⊆ insert e I ∩ insert f I := subset_inter (subset_insert _ _) (subset_insert _ _)
    have := card_le_card this
    omega
  · exact ⟨e, heJ, heI, (hbase e heJ heI).1, (hbase e heJ heI).2, he⟩

/-- The sparse paving matroid (a genuine Mathlib matroid with ground set `univ`). -/
def matroid : Matroid γ :=
  (IndepMatroid.ofFinset Set.univ S.Ind S.ind_empty (fun _ _ hJ hIJ => S.ind_subset hJ hIJ)
    (fun _ _ hI hJ hlt => S.ind_aug hI hJ hlt) (fun _ _ => Set.subset_univ _)).matroid

theorem matroid_E : S.matroid.E = Set.univ := rfl

theorem matroid_indep_iff (I : Finset γ) : S.matroid.Indep (I : Set γ) ↔ S.Ind I := by
  simp [matroid, IndepMatroid.ofFinset_indep]

/-- The rank formula. -/
def rank (B : Finset γ) : ℕ := min S.r (B ∩ S.N).card - if B ∩ S.N ∈ S.H then 1 else 0

theorem eRk_eq (B : Finset γ) [Fintype γ] : S.matroid.eRk (B : Set γ) = (S.rank B : ℕ∞) := by
  apply le_antisymm
  · rw [Matroid.eRk_le_iff]
    intro I hIB hI
    obtain ⟨F, rfl⟩ := (Set.toFinite I).exists_finset_coe
    rw [S.matroid_indep_iff] at hI
    obtain ⟨hFN, hFr, hFH⟩ := hI
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
    have hFB : F ⊆ B ∩ S.N := subset_inter (by exact_mod_cast hIB) hFN
    have h1 := card_le_card hFB
    unfold rank
    split_ifs with hH
    · have hc := S.hcard _ hH
      have : F.card ≠ S.r := fun hEq =>
        hFH ((eq_of_subset_of_card_le hFB (by omega)) ▸ hH)
      omega
    · omega
  · rw [Matroid.le_eRk_iff]
    unfold rank
    split_ifs with hH
    · -- `B ∩ N ∈ H`: drop one element
      have hc := S.hcard _ hH
      obtain ⟨x, hx⟩ : (B ∩ S.N).Nonempty := by
        rw [← card_pos]; have := S.hr; omega
      refine ⟨((B ∩ S.N).erase x : Finset γ), ?_, ?_, ?_⟩
      · intro y hy
        exact (mem_inter.1 (mem_of_mem_erase (by exact_mod_cast hy))).1
      · rw [S.matroid_indep_iff]
        refine ⟨(erase_subset _ _).trans inter_subset_right, ?_, fun h' => ?_⟩
        · rw [card_erase_of_mem hx]; omega
        · have := S.hcard _ h'
          rw [card_erase_of_mem hx] at this
          have := S.hr
          omega
      · rw [Set.encard_coe_eq_coe_finsetCard, card_erase_of_mem hx, hc]
        simp
    · by_cases hle : (B ∩ S.N).card ≤ S.r
      · refine ⟨(B ∩ S.N : Finset γ), ?_, ?_, ?_⟩
        · intro y hy; exact (mem_inter.1 (by exact_mod_cast hy)).1
        · rw [S.matroid_indep_iff]; exact ⟨inter_subset_right, hle, hH⟩
        · rw [Set.encard_coe_eq_coe_finsetCard]; simp [min_eq_right hle]
      · -- more than `r` non-loops: an `(r+1)`-subset contains an independent `r`-subset
        push Not at hle
        obtain ⟨T, hTsub, hTc⟩ := exists_subset_card_eq (s := B ∩ S.N) (n := S.r + 1) (by omega)
        obtain ⟨x, hx⟩ : T.Nonempty := by rw [← card_pos]; omega
        obtain ⟨y, hy, hyx⟩ : ∃ y ∈ T, y ≠ x := by
          by_contra hcon
          push Not at hcon
          have : T ⊆ {x} := fun z hz => mem_singleton.2 (hcon z hz)
          have h1 := card_le_card this
          rw [card_singleton] at h1
          have := S.hr
          omega
        have key : ∃ F ⊆ T, F.card = S.r ∧ F ∉ S.H := by
          by_cases hFx : T.erase x ∈ S.H
          · refine ⟨T.erase y, erase_subset _ _, by rw [card_erase_of_mem hy]; omega,
              fun hFy => ?_⟩
            have hne : T.erase x ≠ T.erase y := by
              intro hEq
              have : x ∈ T.erase y := mem_erase.2 ⟨fun h => hyx h.symm, hx⟩
              rw [← hEq] at this
              simp at this
            have hint := S.hinter _ hFx _ hFy hne
            have hsub : (T.erase x).erase y ⊆ T.erase x ∩ T.erase y := by
              intro z hz
              simp only [mem_erase] at hz
              simp [mem_inter, mem_erase, hz]
            have h1 := card_le_card hsub
            rw [card_erase_of_mem (mem_erase.2 ⟨hyx, hy⟩), card_erase_of_mem hx] at h1
            have := S.hr
            omega
          · exact ⟨T.erase x, erase_subset _ _, by rw [card_erase_of_mem hx]; omega, hFx⟩
        obtain ⟨F, hFT, hFc, hFH⟩ := key
        refine ⟨(F : Finset γ), ?_, ?_, ?_⟩
        · intro z hz
          exact (mem_inter.1 (hTsub (hFT (by exact_mod_cast hz)))).1
        · rw [S.matroid_indep_iff]
          exact ⟨hFT.trans (hTsub.trans inter_subset_right), hFc.le, hFH⟩
        · rw [Set.encard_coe_eq_coe_finsetCard, hFc]
          simp [min_eq_left hle.le]

theorem rk_eq (B : Finset γ) [Fintype γ] : (S.matroid.eRk (B : Set γ)).toNat = S.rank B := by
  rw [S.eRk_eq B]; rfl

theorem rk_univ_eq [Fintype γ] : (S.matroid.eRk Set.univ).toNat = S.rank Finset.univ := by
  rw [← S.rk_eq Finset.univ, Finset.coe_univ]

/-- The genus-`h` Tutte polynomial of a sparse paving matroid, in terms of its rank formula. -/
theorem genusTutte_eq [Fintype γ] (h : ℕ) :
    genusTutte h S.matroid S.matroid_E = gt h S.rank (S.rank Finset.univ) := by
  rw [genusTutte_eq_gt, S.rk_univ_eq]
  congr 1
  funext B
  exact S.rk_eq B

theorem rank_le_card (B : Finset γ) : S.rank B ≤ B.card := by
  unfold rank
  have := card_le_card (inter_subset_left : B ∩ S.N ⊆ B)
  omega

end SP

end GenusTutte
```

### `GTTransfer.lean`

```lean
import GTDefs
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Two transfer principles for the abstract genus polynomial `gt`

1. **Equality by a "Miss" bijection.** Given ground bijections `φ k : α ≃ β` and "bad" families with
   (H1) `Bad' k (φ j B) ↔ Bad k B` for all `j, k`, and (H2) `¬ Bad k B → ρ' (φ k B) = ρ B`, the sums of the
   summands over tuples with some `k` missed by every slot agree. The bijection is
   `A ↦ φ_{pick (Miss A)} ∘ A`.
2. **Inequality by one coefficient.** After `x ↦ x + 1` every summand is a monomial whose exponents
   determine `(|B_s|, ρ(B_s))` at every slot `s`. If a tuple `A₀` on one side has a profile that no tuple
   on the other side has, the coefficient of its monomial is positive on one side and `0` on the other.
-/

open MvPolynomial Finset

set_option linter.unusedSectionVars false

namespace GenusTutte

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {h : ℕ}

/-- Map every probe along an equivalence. -/
def mapT (e : α ≃ β) (A : Fin h → Finset α) : Fin h → Finset β := fun i => (A i).map e.toEmbedding

theorem slotSet_mapT (e : α ≃ β) (A : Fin h → Finset α) (s : Slot h) :
    slotSet (mapT e A) s = (slotSet A s).map e.toEmbedding :=
  slotSet_map e.toEmbedding A s

theorem mapT_symm_mapT (e : α ≃ β) (A : Fin h → Finset α) : mapT e.symm (mapT e A) = A := by
  funext i
  simp [mapT, Finset.map_map]

theorem mapT_mapT_symm (e : α ≃ β) (A : Fin h → Finset β) : mapT e (mapT e.symm A) = A := by
  funext i
  simp [mapT, Finset.map_map]

section Miss

variable {m : ℕ}

/-- Indices `k` such that no slot of `A` is `k`-bad. -/
noncomputable def miss (Bad : Fin (m + 1) → Finset α → Prop) (A : Fin h → Finset α) :
    Finset (Fin (m + 1)) := by
  classical exact univ.filter fun k => ∀ s : Slot h, ¬ Bad k (slotSet A s)

theorem mem_miss (Bad : Fin (m + 1) → Finset α → Prop) (A : Fin h → Finset α) (k : Fin (m + 1)) :
    k ∈ miss Bad A ↔ ∀ s : Slot h, ¬ Bad k (slotSet A s) := by
  classical
  unfold miss
  simp

/-- A choice function on subsets of `Fin (m+1)`. -/
noncomputable def pick (S : Finset (Fin (m + 1))) : Fin (m + 1) :=
  if hS : S.Nonempty then S.min' hS else 0

theorem pick_mem {S : Finset (Fin (m + 1))} (hS : S.Nonempty) : pick S ∈ S := by
  unfold pick; simp only [hS, ↓reduceDIte]; exact S.min'_mem hS

/-- **Equality by a Miss bijection.** -/
theorem sum_miss_eq (ρ : Finset α → ℕ) (ρ' : Finset β → ℕ) (R : ℕ)
    (φ : Fin (m + 1) → α ≃ β) (Bad : Fin (m + 1) → Finset α → Prop)
    (Bad' : Fin (m + 1) → Finset β → Prop)
    (H1 : ∀ j k B, Bad' k (B.map (φ j).toEmbedding) ↔ Bad k B)
    (H2 : ∀ k B, ¬ Bad k B → ρ' (B.map (φ k).toEmbedding) = ρ B) :
    ∑ A ∈ univ.filter (fun A : Fin h → Finset α => (miss Bad A).Nonempty), term h ρ R A =
      ∑ A ∈ univ.filter (fun A : Fin h → Finset β => (miss Bad' A).Nonempty), term h ρ' R A := by
  have hmiss : ∀ j (A : Fin h → Finset α), miss Bad' (mapT (φ j) A) = miss Bad A := by
    intro j A
    ext k
    simp only [mem_miss, slotSet_mapT, H1]
  have hmiss' : ∀ j (A : Fin h → Finset β), miss Bad (mapT (φ j).symm A) = miss Bad' A := by
    intro j A
    rw [← hmiss j (mapT (φ j).symm A), mapT_mapT_symm]
  refine Finset.sum_nbij' (fun A => mapT (φ (pick (miss Bad A))) A)
    (fun A => mapT (φ (pick (miss Bad' A))).symm A) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA ⊢
    rwa [hmiss]
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA ⊢
    rwa [hmiss']
  · intro A _
    simp only [hmiss, mapT_symm_mapT]
  · intro A _
    simp only [hmiss', mapT_mapT_symm]
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA
    have hk := (mem_miss Bad A _).1 (pick_mem hA)
    symm
    apply term_congr
    · intro s; rw [slotSet_mapT, card_map]
    · intro s; rw [slotSet_mapT]; exact H2 _ _ (hk s)

end Miss

/-! ## The coefficient argument -/

section Coeff

/-- The exponent vector of a summand after `x ↦ x + 1`. -/
noncomputable def deg (ρ : Finset α → ℕ) (R : ℕ) (A : Fin h → Finset α) : Slot h × Bool →₀ ℕ :=
  ∑ s : Slot h, (Finsupp.single (s, false) (R - ρ (slotSet A s)) +
    Finsupp.single (s, true) ((slotSet A s).card - ρ (slotSet A s)))

theorem deg_apply (ρ : Finset α → ℕ) (R : ℕ) (A : Fin h → Finset α) (s : Slot h) (b : Bool) :
    deg ρ R A (s, b) = if b then (slotSet A s).card - ρ (slotSet A s) else R - ρ (slotSet A s) := by
  classical
  unfold deg
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · cases b <;> simp
  · intro s' _ hs'
    cases b <;> simp [hs']
  · simp

/-- The substitution `x ↦ x + 1`. -/
noncomputable def shift : MvPolynomial (Slot h × Bool) ℤ →ₐ[ℤ] MvPolynomial (Slot h × Bool) ℤ :=
  aeval fun v => X v + 1

theorem shift_term (ρ : Finset α → ℕ) (R : ℕ) (A : Fin h → Finset α) :
    shift (term h ρ R A) = monomial (deg ρ R A) 1 := by
  unfold term deg shift
  rw [monomial_sum_one, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [map_mul, map_pow, map_sub, aeval_X, map_one, add_sub_cancel_right]
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

theorem coeff_shift_gt (ρ : Finset α → ℕ) (R : ℕ) (d : Slot h × Bool →₀ ℕ) :
    (shift (gt h ρ R)).coeff d =
      ∑ A : Fin h → Finset α, if deg ρ R A = d then (1 : ℤ) else 0 := by
  unfold gt
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [shift_term, coeff_monomial]

/-- **Inequality by one coefficient.** -/
theorem gt_ne_of_witness (ρ : Finset α → ℕ) (ρ' : Finset β → ℕ) (R : ℕ)
    (hR : ∀ B, ρ B ≤ R) (hc : ∀ B, ρ B ≤ B.card) (hR' : ∀ B, ρ' B ≤ R)
    (hc' : ∀ B, ρ' B ≤ B.card) (A₀ : Fin h → Finset α)
    (hno : ∀ A : Fin h → Finset β, ¬ ∀ s, (slotSet A s).card = (slotSet A₀ s).card ∧
      ρ' (slotSet A s) = ρ (slotSet A₀ s)) :
    gt h ρ R ≠ gt h ρ' R := by
  intro hEq
  have h1 := congrArg (fun P => (shift P).coeff (deg ρ R A₀)) hEq
  simp only [coeff_shift_gt] at h1
  have hzero : (∑ A : Fin h → Finset β, if deg ρ' R A = deg ρ R A₀ then (1 : ℤ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun A _ => ?_
    split_ifs with hd
    swap; · rfl
    exfalso
    apply hno A
    intro s
    have e1 := congrArg (fun d => d (s, false)) hd
    have e2 := congrArg (fun d => d (s, true)) hd
    simp only [deg_apply, Bool.false_eq_true, ite_false, ite_true] at e1 e2
    have := hR (slotSet A₀ s); have := hc (slotSet A₀ s)
    have := hR' (slotSet A s); have := hc' (slotSet A s)
    constructor <;> omega
  have hpos : (1 : ℤ) ≤ ∑ A : Fin h → Finset α, if deg ρ R A = deg ρ R A₀ then (1 : ℤ) else 0 := by
    have := Finset.single_le_sum (f := fun A : Fin h → Finset α =>
      if deg ρ R A = deg ρ R A₀ then (1 : ℤ) else 0) (fun A _ => by split_ifs <;> norm_num)
      (mem_univ A₀)
    simpa using this
  rw [h1, hzero] at hpos
  norm_num at hpos

end Coeff

end GenusTutte
```

### `GTPad.lean`

```lean
import GTSparse
import GTTransfer
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Loop padding and assembly of the endpoint from two gadgets

A *gadget* is a loopless sparse paving matroid on a finite type `α` (ground set everything). Padding with
`i` loops gives a sparse paving matroid with loops on `α ⊕ Fin i ≃ Fin (a + i)`. Its genus-`h` polynomial
factors as (gadget polynomial) × (polynomial of `i` loops), and the second factor is nonzero (its value at
all variables `= 2` is the number of tuples). So equality and inequality of the gadget polynomials pass to
all paddings, giving the two infinite sequences of the conjecture with `n i = a + i`.
-/

open MvPolynomial Finset

set_option linter.unusedSectionVars false

namespace GenusTutte

variable {h : ℕ}

/-! ## Transport along an equivalence -/

theorem gt_equiv {γ δ : Type*} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (E : γ ≃ δ) (ρ : Finset δ → ℕ) (R : ℕ) :
    gt h ρ R = gt h (fun B => ρ (B.map E.toEmbedding)) R := by
  unfold gt
  let T : (Fin h → Finset γ) ≃ (Fin h → Finset δ) :=
    ⟨mapT E, mapT E.symm, fun A => mapT_symm_mapT E A, fun A => mapT_mapT_symm E A⟩
  symm
  refine Fintype.sum_equiv T _ _ fun A => ?_
  apply (term_congr h _ _ R _ _ _ _).symm
  · intro s; show (slotSet (mapT E A) s).card = _; rw [slotSet_mapT, card_map]
  · intro s; show ρ (slotSet (mapT E A) s) = _; rw [slotSet_mapT]

/-! ## Factorization over a sum type -/

section Split

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem slotSet_toLeft (A : Fin h → Finset (α ⊕ β)) (s : Slot h) :
    (slotSet A s).toLeft = slotSet (fun i => (A i).toLeft) s := by
  rcases s with i | ⟨p, b⟩
  · rfl
  · cases b
    · simp [slotSet, toLeft_inter]
    · simp [slotSet, toLeft_union]

theorem slotSet_toRight (A : Fin h → Finset (α ⊕ β)) (s : Slot h) :
    (slotSet A s).toRight = slotSet (fun i => (A i).toRight) s := by
  rcases s with i | ⟨p, b⟩
  · rfl
  · cases b
    · simp [slotSet, toRight_inter]
    · simp [slotSet, toRight_union]

theorem term_split (ρ : Finset α → ℕ) (R : ℕ) (hρ : ∀ B, ρ B ≤ B.card)
    (A : Fin h → Finset (α ⊕ β)) :
    term h (fun B => ρ B.toLeft) R A =
      term h ρ R (fun i => (A i).toLeft) * term h (fun _ : Finset β => 0) 0 (fun i => (A i).toRight) := by
  unfold term
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  dsimp only
  have hcard := (card_toLeft_add_card_toRight (u := slotSet A s)).symm
  rw [slotSet_toLeft, slotSet_toRight] at hcard
  rw [slotSet_toLeft]
  have hle := hρ (slotSet (fun i => (A i).toLeft) s)
  rw [show (slotSet A s).card - ρ (slotSet (fun i => (A i).toLeft) s) =
      ((slotSet (fun i => (A i).toLeft) s).card - ρ (slotSet (fun i => (A i).toLeft) s)) +
        (slotSet (fun i => (A i).toRight) s).card by omega, pow_add]
  simp only [Nat.sub_zero, pow_zero, one_mul]
  ring

/-- Tuples on a sum type are pairs of tuples. -/
def splitT : (Fin h → Finset (α ⊕ β)) ≃ (Fin h → Finset α) × (Fin h → Finset β) where
  toFun A := (fun i => (A i).toLeft, fun i => (A i).toRight)
  invFun P := fun i => (P.1 i).disjSum (P.2 i)
  left_inv A := by funext i; simp [toLeft_disjSum_toRight]
  right_inv P := by ext <;> simp

theorem gt_sum (ρ : Finset α → ℕ) (R : ℕ) (hρ : ∀ B, ρ B ≤ B.card) :
    gt h (fun B : Finset (α ⊕ β) => ρ B.toLeft) R =
      gt h ρ R * gt h (fun _ : Finset β => 0) 0 := by
  unfold gt
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv splitT _ _ fun A => ?_
  rw [term_split ρ R hρ]
  rfl

/-- The polynomial of a set of loops is nonzero. -/
theorem gt_loops_ne_zero : gt h (fun _ : Finset β => 0) 0 ≠ 0 := by
  intro h0
  have := congrArg (MvPolynomial.eval (fun _ : Slot h × Bool => (2 : ℤ))) h0
  simp only [gt, term, map_sum, map_prod, map_mul, map_pow, map_sub, eval_X, map_one, map_zero] at this
  norm_num at this

end Split

/-! ## Gadgets and their paddings -/

/-- A loopless sparse paving matroid on a finite type (ground set everything). -/
structure Gadget (α : Type*) [DecidableEq α] where
  r : ℕ
  H : Finset (Finset α)
  hr : 1 ≤ r
  hcard : ∀ B ∈ H, B.card = r
  hinter : ∀ B ∈ H, ∀ B' ∈ H, B ≠ B' → (B ∩ B').card + 2 ≤ r

namespace Gadget

variable {α : Type*} [Fintype α] [DecidableEq α] (G : Gadget α)

/-- The rank formula of the gadget. -/
def rank (B : Finset α) : ℕ := min G.r B.card - if B ∈ G.H then 1 else 0

theorem rank_le_card (B : Finset α) : G.rank B ≤ B.card := by unfold rank; omega

theorem rank_le_r (B : Finset α) : G.rank B ≤ G.r := by unfold rank; omega

variable {a : ℕ} (e : α ≃ Fin a) (i : ℕ)

/-- The identification `α ⊕ Fin i ≃ Fin (a + i)`. -/
def padEquiv : α ⊕ Fin i ≃ Fin (a + i) := (Equiv.sumCongr e (Equiv.refl (Fin i))).trans finSumFinEquiv

/-- The embedding of the gadget into the padded ground set. -/
def padEmb : α ↪ Fin (a + i) := Function.Embedding.inl.trans (padEquiv e i).toEmbedding

/-- The gadget padded with `i` loops, as sparse paving data on `Fin (a + i)`. -/
def pad : SP (Fin (a + i)) where
  N := univ.map (padEmb e i)
  r := G.r
  H := G.H.image fun B => B.map (padEmb e i)
  hr := G.hr
  hsub := by
    intro B hB
    obtain ⟨B₀, -, rfl⟩ := mem_image.1 hB
    exact map_subset_map.2 (subset_univ _)
  hcard := by
    intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB
    rw [card_map, G.hcard _ hB₀]
  hinter := by
    intro B hB B' hB' hne
    obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB
    obtain ⟨B₁, hB₁, rfl⟩ := mem_image.1 hB'
    rw [← map_inter, card_map]
    exact G.hinter _ hB₀ _ hB₁ fun h' => hne (h' ▸ rfl)

theorem map_padEquiv_inter (B : Finset (α ⊕ Fin i)) :
    B.map (padEquiv e i).toEmbedding ∩ univ.map (padEmb e i) = B.toLeft.map (padEmb e i) := by
  ext y
  simp only [mem_inter, mem_map, mem_univ, true_and, mem_toLeft]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, x, hx⟩
    have : z = Sum.inl x := (padEquiv e i).injective hx.symm
    subst this
    exact ⟨x, hz, hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨Sum.inl x, hx, rfl⟩, x, rfl⟩

theorem pad_rank_map (B : Finset (α ⊕ Fin i)) :
    (G.pad e i).rank (B.map (padEquiv e i).toEmbedding) = G.rank B.toLeft := by
  unfold SP.rank rank
  have hN : (G.pad e i).N = univ.map (padEmb e i) := rfl
  rw [hN, map_padEquiv_inter, card_map]
  congr 2
  apply propext
  show B.toLeft.map (padEmb e i) ∈ G.H.image (fun B => B.map (padEmb e i)) ↔ _
  rw [mem_image]
  constructor
  · rintro ⟨B₀, hB₀, hEq⟩
    rwa [← map_inj.1 hEq]
  · intro hB
    exact ⟨_, hB, rfl⟩

theorem pad_rank_univ : (G.pad e i).rank univ = G.rank univ := by
  have := G.pad_rank_map e i univ
  rwa [map_univ_equiv, toLeft_univ] at this

/-- **Factorization.** -/
theorem genusTutte_pad (h : ℕ) :
    genusTutte h (G.pad e i).matroid (G.pad e i).matroid_E =
      gt h G.rank (G.rank univ) * gt h (fun _ : Finset (Fin i) => 0) 0 := by
  rw [SP.genusTutte_eq, gt_equiv (padEquiv e i), pad_rank_univ]
  simp only [pad_rank_map]
  exact gt_sum G.rank _ G.rank_le_card

end Gadget

/-- **Assembly**: two gadgets of the same size whose genus-`g` polynomials agree and whose genus-`(g+1)`
polynomials differ give the conjecture for `g` (pad both with `i` loops, `n i = a + i`). -/
theorem conj_of_gadgets {g a : ℕ} {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (GX : Gadget α) (GY : Gadget β) (eα : α ≃ Fin a) (eβ : β ≃ Fin a)
    (heq : gt g GX.rank (GX.rank univ) = gt g GY.rank (GY.rank univ))
    (hne : gt (g + 1) GX.rank (GX.rank univ) ≠ gt (g + 1) GY.rank (GY.rank univ)) :
    MiezakiConj512 g := by
  refine ⟨fun i => a + i, fun i => (GX.pad eα i).matroid, fun i => (GY.pad eβ i).matroid,
    fun i => (GX.pad eα i).matroid_E, fun i => (GY.pad eβ i).matroid_E,
    fun _ _ hij => Nat.add_lt_add_left hij a, fun i => ⟨?_, ?_⟩⟩
  · rw [Gadget.genusTutte_pad, Gadget.genusTutte_pad, heq]
  · rw [Gadget.genusTutte_pad, Gadget.genusTutte_pad]
    intro hcon
    exact hne (mul_right_cancel₀ gt_loops_ne_zero hcon)

end GenusTutte
```

### `Parity.lean`

```lean
import GTPad
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# The parity gadget (PROOF-361823 §4)

For `t = s + 4` coordinates, `E t p = {x ∈ {0,1}^t : parity x = p}` and `S p k c = {x ∈ E t p : x_k = c}`.
The circuit-hyperplanes are `S p k true`, `k < t`; the rank is `r = 2^(t-2)`. Flipping coordinate `j`
is a bijection `τ_j : E t 0 ≃ E t 1`. All counts are obtained from flips.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace GenusTutte

namespace Parity

variable {t : ℕ}

theorem par_aux : ∀ (b : Bool) (S : ZMod 2),
    ((if (!b) = true then 1 else 0) + S) = ((if b = true then 1 else 0) + S) + 1 := by decide

theorem zmod_succ_eq : ∀ a b : ZMod 2, a ≠ b → a + 1 = b := by decide

theorem zmod_add_one_eq_zero : ∀ a : ZMod 2, a + 1 = 0 ↔ a = 1 := by decide

theorem zmod_add_one_eq_one : ∀ a : ZMod 2, a + 1 = 1 ↔ a = 0 := by decide

/-- Parity of a Boolean vector. -/
def par (x : Fin t → Bool) : ZMod 2 := ∑ i, if x i then 1 else 0

/-- Flip coordinate `m`. -/
def flip (m : Fin t) (x : Fin t → Bool) : Fin t → Bool := Function.update x m (!x m)

theorem flip_apply (m k : Fin t) (x : Fin t → Bool) :
    flip m x k = if k = m then !x k else x k := by
  unfold flip
  by_cases h : k = m
  · subst h; simp
  · simp [h]

theorem flip_flip (m : Fin t) (x : Fin t → Bool) : flip m (flip m x) = x := by
  funext k
  rw [flip_apply, flip_apply]
  split_ifs <;> simp

theorem par_flip (m : Fin t) (x : Fin t → Bool) : par (flip m x) = par x + 1 := by
  unfold par
  rw [← Finset.add_sum_erase _ _ (mem_univ m), ← Finset.add_sum_erase _ _ (mem_univ m)]
  have : ∑ i ∈ univ.erase m, (if flip m x i then (1 : ZMod 2) else 0) =
      ∑ i ∈ univ.erase m, (if x i then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [flip_apply, if_neg' (Finset.ne_of_mem_erase hi)]
  rw [this, flip_apply, if_pos' rfl]
  exact par_aux _ _

/-- The parity classes. -/
abbrev E (t : ℕ) (p : ZMod 2) := {x : Fin t → Bool // par x = p}

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by decide +revert

/-- The flip bijection between the two parity classes. -/
def tau (m : Fin t) : E t 0 ≃ E t 1 where
  toFun x := ⟨flip m x.1, by rw [par_flip, x.2]; rfl⟩
  invFun y := ⟨flip m y.1, by rw [par_flip, y.2]; decide⟩
  left_inv x := Subtype.ext (flip_flip m x.1)
  right_inv y := Subtype.ext (flip_flip m y.1)

/-- Coordinate half-spaces of a parity class. -/
def S (p : ZMod 2) (k : Fin t) (c : Bool) : Finset (E t p) := univ.filter fun x => x.1 k = c

theorem mem_S {p : ZMod 2} {k : Fin t} {c : Bool} {x : E t p} : x ∈ S p k c ↔ x.1 k = c := by
  simp [S]

/-! ## Counting with flips -/

theorem card_filter_flip (m : Fin t) (P Q : (Fin t → Bool) → Prop) [DecidablePred P]
    [DecidablePred Q] (hPQ : ∀ x, Q x ↔ P (flip m x)) :
    (univ.filter P).card = (univ.filter Q).card := by
  refine Finset.card_bij' (fun x _ => flip m x) (fun x _ => flip m x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hPQ, flip_flip]; exact hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact (hPQ x).1 hx
  · intro x _; exact flip_flip m x
  · intro x _; exact flip_flip m x

theorem card_subtype_filter (p : ZMod 2) (P : (Fin t → Bool) → Prop) [DecidablePred P] :
    (univ.filter fun y : E t p => P y.1).card = (univ.filter fun x => par x = p ∧ P x).card := by
  refine Finset.card_bij' (fun y _ => y.1) (fun x hx => ⟨x, (mem_filter.1 hx).2.1⟩) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact ⟨y.2, hy⟩
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.2
  · intro y _; rfl
  · intro x _; rfl

/-- Halving by parity: if `P` is invariant under flipping `m`, each parity class has half of `P`. -/
theorem card_par_half (m : Fin t) (p : ZMod 2) (P : (Fin t → Bool) → Prop) [DecidablePred P]
    (hP : ∀ x, P (flip m x) ↔ P x) :
    2 * (univ.filter fun x => par x = p ∧ P x).card = (univ.filter P).card := by
  have h01 : (univ.filter fun x => par x = 0 ∧ P x).card =
      (univ.filter fun x => par x = 1 ∧ P x).card := by
    apply card_filter_flip m
    intro x
    rw [par_flip, hP, zmod_add_one_eq_zero]
  have hsplit : (univ.filter fun x => par x = 0 ∧ P x).card +
      (univ.filter fun x => par x = 1 ∧ P x).card = (univ.filter P).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases zmod2_cases (par x) with h | h <;> simp [h]
    · rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      rw [h1.1] at h2
      exact absurd h2.1 (by decide)
  rcases zmod2_cases p with rfl | rfl <;> omega

variable (s : ℕ)

theorem card_univ_cube : (univ : Finset (Fin (s + 4) → Bool)).card = 2 ^ (s + 4) := by
  simp

theorem card_coord (k : Fin (s + 4)) (c : Bool) :
    (univ.filter fun x : Fin (s + 4) → Bool => x k = c).card = 2 ^ (s + 3) := by
  have h1 : (univ.filter fun x : Fin (s + 4) → Bool => x k = c).card =
      (univ.filter fun x : Fin (s + 4) → Bool => ¬ x k = c).card := by
    apply card_filter_flip k
    intro x
    rw [flip_apply, if_pos' rfl]
    cases x k <;> cases c <;> simp
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (s + 4) → Bool))) (fun x => x k = c)
  rw [card_univ_cube, ← h1] at h2
  have e : 2 ^ (s + 4) = 2 ^ (s + 3) * 2 := pow_succ 2 (s + 3)
  omega

theorem card_coord2 (k k' : Fin (s + 4)) (hk : k ≠ k') (c c' : Bool) :
    (univ.filter fun x : Fin (s + 4) → Bool => x k = c ∧ x k' = c').card = 2 ^ (s + 2) := by
  have h1 : (univ.filter fun x : Fin (s + 4) → Bool => x k = c ∧ x k' = c').card =
      (univ.filter fun x : Fin (s + 4) → Bool => x k = c ∧ ¬ x k' = c').card := by
    apply card_filter_flip k'
    intro x
    rw [flip_apply, flip_apply, if_pos' rfl, if_neg' hk]
    cases x k' <;> cases c' <;> simp
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ.filter fun x : Fin (s + 4) → Bool => x k = c)) (fun x => x k' = c')
  rw [Finset.filter_filter, Finset.filter_filter, card_coord, ← h1] at h2
  have e : 2 ^ (s + 3) = 2 ^ (s + 2) * 2 := pow_succ 2 (s + 2)
  omega

/-- An index outside three given ones. -/
theorem exists_other (k1 k2 k3 : Fin (s + 4)) : ∃ m, m ≠ k1 ∧ m ≠ k2 ∧ m ≠ k3 := by
  by_contra hcon
  push Not at hcon
  have : (univ : Finset (Fin (s + 4))) ⊆ {k1, k2, k3} := by
    intro m _
    by_cases h1 : m = k1
    · simp [h1]
    by_cases h2 : m = k2
    · simp [h2]
    simp [hcon m h1 h2]
  have := card_le_card this
  have := Finset.card_le_three (a := k1) (b := k2) (c := k3)
  simp at *
  omega

theorem card_E (p : ZMod 2) : (univ : Finset (E (s + 4) p)).card = 2 ^ (s + 3) := by
  have h := card_subtype_filter p (fun _ : Fin (s + 4) → Bool => True)
  simp only [and_true, filter_true_of_mem (fun _ _ => trivial)] at h
  rw [h]
  have := card_par_half 0 p (fun _ : Fin (s + 4) → Bool => True) (fun _ => Iff.rfl)
  simp only [and_true, filter_true_of_mem (fun _ _ => trivial), card_univ_cube] at this
  have e : 2 ^ (s + 4) = 2 ^ (s + 3) * 2 := pow_succ 2 (s + 3)
  omega

theorem card_S (p : ZMod 2) (k : Fin (s + 4)) (c : Bool) :
    (S p k c).card = 2 ^ (s + 2) := by
  unfold S
  refine (card_subtype_filter p (fun x : Fin (s + 4) → Bool => x k = c)).trans ?_
  obtain ⟨m, hm, -, -⟩ := exists_other s k k k
  have := card_par_half m p (fun x : Fin (s + 4) → Bool => x k = c)
    (fun x => by rw [flip_apply, if_neg' (Ne.symm hm)])
  rw [card_coord] at this
  have e : 2 ^ (s + 3) = 2 ^ (s + 2) * 2 := pow_succ 2 (s + 2)
  omega

theorem card_S_inter (p : ZMod 2) (k k' : Fin (s + 4)) (hk : k ≠ k') (c c' : Bool) :
    (S p k c ∩ S p k' c').card = 2 ^ (s + 1) := by
  have : S p k c ∩ S p k' c' = univ.filter fun y : E (s + 4) p => y.1 k = c ∧ y.1 k' = c' := by
    ext y; simp [S]
  rw [this]
  refine (card_subtype_filter p (fun x : Fin (s + 4) → Bool => x k = c ∧ x k' = c')).trans ?_
  obtain ⟨m, hm, hm', -⟩ := exists_other s k k' k
  have := card_par_half m p (fun x : Fin (s + 4) → Bool => x k = c ∧ x k' = c')
    (fun x => by rw [flip_apply, flip_apply, if_neg' (Ne.symm hm), if_neg' (Ne.symm hm')])
  rw [card_coord2 s k k' hk] at this
  have e : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := pow_succ 2 (s + 1)
  omega

theorem card_S_union (p : ZMod 2) (k k' : Fin (s + 4)) (hk : k ≠ k') (c c' : Bool) :
    (S p k c ∪ S p k' c').card = 3 * 2 ^ (s + 1) := by
  have h := Finset.card_union_add_card_inter (S p k c) (S p k' c')
  rw [card_S, card_S, card_S_inter s p k k' hk] at h
  have e : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := pow_succ 2 (s + 1)
  omega

/-- **Three-coordinate surjectivity** of a parity class (needs `t ≥ 4`). -/
theorem proj3 (p : ZMod 2) (k1 k2 k3 : Fin (s + 4)) (h12 : k1 ≠ k2) (h13 : k1 ≠ k3)
    (h23 : k2 ≠ k3) (b1 b2 b3 : Bool) :
    ∃ x : E (s + 4) p, x.1 k1 = b1 ∧ x.1 k2 = b2 ∧ x.1 k3 = b3 := by
  let y : Fin (s + 4) → Bool := fun i => if i = k1 then b1 else if i = k2 then b2 else
    if i = k3 then b3 else false
  have hy1 : y k1 = b1 := by simp [y]
  have hy2 : y k2 = b2 := by simp [y, Ne.symm h12]
  have hy3 : y k3 = b3 := by simp [y, Ne.symm h13, Ne.symm h23]
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_other s k1 k2 k3
  by_cases hp : par y = p
  · exact ⟨⟨y, hp⟩, hy1, hy2, hy3⟩
  · refine ⟨⟨flip m y, ?_⟩, ?_, ?_, ?_⟩
    · rw [par_flip]
      exact zmod_succ_eq _ _ hp
    · simp [flip_apply, Ne.symm hm1, hy1]
    · simp [flip_apply, Ne.symm hm2, hy2]
    · simp [flip_apply, Ne.symm hm3, hy3]

/-- Two-coordinate surjectivity. -/
theorem proj2 (p : ZMod 2) (k1 k2 : Fin (s + 4)) (h12 : k1 ≠ k2) (b1 b2 : Bool) :
    ∃ x : E (s + 4) p, x.1 k1 = b1 ∧ x.1 k2 = b2 := by
  obtain ⟨m, hm1, hm2, -⟩ := exists_other s k1 k2 k1
  obtain ⟨x, h1, h2, -⟩ := proj3 s p k1 k2 m h12 (Ne.symm hm1) (Ne.symm hm2) b1 b2 false
  exact ⟨x, h1, h2⟩

theorem S_inj (p : ZMod 2) {k k' : Fin (s + 4)} {c c' : Bool} (h : S p k c = S p k' c') :
    k = k' ∧ c = c' := by
  by_cases hk : k = k'
  · subst hk
    refine ⟨rfl, ?_⟩
    obtain ⟨m, hm, -, -⟩ := exists_other s k k k
    obtain ⟨x, hx, -⟩ := proj2 s p k m (Ne.symm hm) c false
    have : x ∈ S p k c := mem_S.2 hx
    rw [h, mem_S] at this
    rw [← hx, this]
  · exfalso
    obtain ⟨x, hx, hx'⟩ := proj2 s p k k' hk c (!c')
    have : x ∈ S p k c := mem_S.2 hx
    rw [h, mem_S, hx'] at this
    cases c' <;> simp at this

/-! ## Flips and the half-spaces -/

theorem map_tau_S (j k : Fin (s + 4)) (c : Bool) :
    (S 0 k c).map (tau j).toEmbedding = S 1 k (if k = j then !c else c) := by
  ext y
  simp only [mem_map_equiv, mem_S]
  show flip j y.1 k = c ↔ _
  rw [flip_apply]
  split_ifs <;> cases y.1 k <;> cases c <;> simp

theorem map_tau_symm_S (j k : Fin (s + 4)) (c : Bool) :
    (S 1 k c).map (tau j).symm.toEmbedding = S 0 k (if k = j then !c else c) := by
  ext y
  simp only [mem_map_equiv, Equiv.symm_symm, mem_S]
  show flip j y.1 k = c ↔ _
  rw [flip_apply]
  split_ifs <;> cases y.1 k <;> cases c <;> simp

/-! ## The gadget -/

/-- The parity gadget for parity `p`: rank `2^(s+2)`, circuit-hyperplanes `S p k true`. -/
def gadget (p : ZMod 2) : Gadget (E (s + 4) p) where
  r := 2 ^ (s + 2)
  H := univ.image fun k => S p k true
  hr := Nat.one_le_two_pow
  hcard := by
    intro B hB
    obtain ⟨k, -, rfl⟩ := mem_image.1 hB
    exact card_S s p k true
  hinter := by
    intro B hB B' hB' hne
    obtain ⟨k, -, rfl⟩ := mem_image.1 hB
    obtain ⟨k', -, rfl⟩ := mem_image.1 hB'
    have hk : k ≠ k' := fun h => hne (h ▸ rfl)
    rw [card_S_inter s p k k' hk]
    have e : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := pow_succ 2 (s + 1)
    have e' : 2 ^ (s + 1) = 2 ^ s * 2 := pow_succ 2 s
    have := Nat.one_le_two_pow (n := s)
    omega

theorem mem_gadget_H (p : ZMod 2) (B : Finset (E (s + 4) p)) :
    B ∈ (gadget s p).H ↔ ∃ k, B = S p k true := by
  simp [gadget, eq_comm]

theorem S_mem_H_iff (p : ZMod 2) (k : Fin (s + 4)) (c : Bool) :
    S p k c ∈ (gadget s p).H ↔ c = true := by
  rw [mem_gadget_H]
  constructor
  · rintro ⟨k', h⟩; exact (S_inj s p h).2
  · rintro rfl; exact ⟨k, rfl⟩

theorem not_mem_H_of_card (p : ZMod 2) (B : Finset (E (s + 4) p)) (hB : B.card ≠ 2 ^ (s + 2)) :
    B ∉ (gadget s p).H := fun h => hB ((gadget s p).hcard B h)

theorem gadget_rank_univ (p : ZMod 2) : (gadget s p).rank univ = 2 ^ (s + 2) := by
  have hc := card_E s p
  have e : 2 ^ (s + 3) = 2 ^ (s + 2) * 2 := pow_succ 2 (s + 2)
  have := Nat.one_le_two_pow (n := s + 2)
  have hn : (univ : Finset (E (s + 4) p)) ∉ (gadget s p).H :=
    not_mem_H_of_card s p _ (by omega)
  unfold Gadget.rank
  rw [if_neg' hn, hc]
  show min (2 ^ (s + 2)) _ - 0 = _
  omega

end Parity

end GenusTutte
```

### `Rigidity.lean`

```lean
import Parity

/-!
# The Boolean-probe rigidity lemma (PROOF-361823 §3, in the form needed by the bijection)

Let `t = s + 4` and let `A` be a `t`-tuple of subsets of a parity class `E t p`. Suppose every coordinate
half-space family is hit: for each `k` some slot of `A` equals `S p k c` for some `c`. Then each `k` is hit
by a *singleton* slot, i.e. some `A i` equals `S p k c`.

Proof (graph-free). Every slot is an intersection or a union over its input set `In(σ)` (one or two
indices; singletons count as intersections). Write `T_k` for the chosen slot set of `k`. A parity class is
onto any two and any three coordinates, so no `T_k ⊆ T_k'` (`k ≠ k'`), no `T_k₁ ∩ T_k₂ ⊆ T_k` and no
`T_k ⊆ T_k₁ ∪ T_k₂` for distinct `k, k₁, k₂`. From these, every output `k` has a *private* input (one not used
by any other output): otherwise both inputs `a, b` of `k` are used by outputs `k₁, k₂ ≠ k`, and each type
combination yields one of the forbidden inclusions. A choice of private inputs is an injective map
`Fin t → Fin t`, hence onto, so no output has a second input: all chosen slots are singletons.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace GenusTutte

theorem slotIn_eq_pair {h : ℕ} (σ : Slot h) : ∃ a b, slotIn σ = {a, b} := by
  rcases σ with i | ⟨q, b⟩
  · exact ⟨i, i, by simp [slotIn]⟩
  · exact ⟨q.1.1, q.1.2, rfl⟩

/-- Private inputs force every input set to have at most one element. -/
theorem card_le_one_of_private {n : ℕ} (In : Fin n → Finset (Fin n))
    (hpriv : ∀ k, ∃ x ∈ In k, ∀ k', k' ≠ k → x ∉ In k') : ∀ k, (In k).card ≤ 1 := by
  choose π hπ hπp using hpriv
  have hinj : Function.Injective π := by
    intro k k' hkk
    by_contra hne
    exact hπp k k' (Ne.symm hne) (hkk ▸ hπ k')
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro k
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨ka, rfl⟩ := hsurj a
  obtain ⟨kb, rfl⟩ := hsurj b
  have hka : ka = k := by
    by_contra hne; exact hπp ka k (Ne.symm hne) ha
  have hkb : kb = k := by
    by_contra hne; exact hπp kb k (Ne.symm hne) hb
  rw [hka, hkb]

namespace Parity

variable (s : ℕ)

/-- **Rigidity lemma.** -/
theorem rigidity (p : ZMod 2) (A : Fin (s + 4) → Finset (E (s + 4) p))
    (hA : ∀ k, ∃ σ : Slot (s + 4), ∃ c, slotSet A σ = S p k c) :
    ∀ k, ∃ i c, A i = S p k c := by
  choose σ c hσ using hA
  have memT : ∀ k (x : E (s + 4) p), x ∈ slotSet A (σ k) ↔ x.1 k = c k := fun k x => by
    rw [hσ, mem_S]
  -- no inclusion between two outputs
  have nsub : ∀ k k', k ≠ k' → ¬ (∀ x, x ∈ slotSet A (σ k) → x ∈ slotSet A (σ k')) := by
    intro k k' hk hsub
    obtain ⟨x, h1, h2⟩ := proj2 s p k k' hk (c k) (!c k')
    have := (memT k' x).1 (hsub x ((memT k x).2 h1))
    rw [h2] at this
    cases hc : c k' <;> simp [hc] at this
  -- no `T₁ ∩ T₂ ⊆ T` and no `T ⊆ T₁ ∪ T₂`
  have n3cap : ∀ k1 k2 k, k1 ≠ k2 → k1 ≠ k → k2 ≠ k →
      ¬ (∀ x, x ∈ slotSet A (σ k1) → x ∈ slotSet A (σ k2) → x ∈ slotSet A (σ k)) := by
    intro k1 k2 k h12 h1 h2 hsub
    obtain ⟨x, e1, e2, e3⟩ := proj3 s p k1 k2 k h12 h1 h2 (c k1) (c k2) (!c k)
    have := (memT k x).1 (hsub x ((memT k1 x).2 e1) ((memT k2 x).2 e2))
    rw [e3] at this
    cases hc : c k <;> simp [hc] at this
  have n3cup : ∀ k1 k2 k, k1 ≠ k2 → k1 ≠ k → k2 ≠ k →
      ¬ (∀ x, x ∈ slotSet A (σ k) → x ∈ slotSet A (σ k1) ∨ x ∈ slotSet A (σ k2)) := by
    intro k1 k2 k h12 h1 h2 hsub
    obtain ⟨x, e1, e2, e3⟩ := proj3 s p k1 k2 k h12 h1 h2 (!c k1) (!c k2) (c k)
    rcases hsub x ((memT k x).2 e3) with h | h
    · have := (memT k1 x).1 h; rw [e1] at this; cases hc : c k1 <;> simp [hc] at this
    · have := (memT k2 x).1 h; rw [e2] at this; cases hc : c k2 <;> simp [hc] at this
  -- every output has a private input
  have hpriv : ∀ k, ∃ x ∈ slotIn (σ k), ∀ k', k' ≠ k → x ∉ slotIn (σ k') := by
    intro k
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := slotIn_eq_pair (σ k)
    have ha : a ∈ slotIn (σ k) := by rw [hab]; simp
    have hb : b ∈ slotIn (σ k) := by rw [hab]; simp
    obtain ⟨k1, hk1, ha1⟩ := hcon a ha
    obtain ⟨k2, hk2, hb2⟩ := hcon b hb
    have hcov : ∀ i ∈ slotIn (σ k), i ∈ slotIn (σ k1) ∨ i ∈ slotIn (σ k2) := by
      intro i hi
      rw [hab, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Or.inl ha1
      · exact Or.inr hb2
    cases hc : slotCap (σ k) <;> cases hc1 : slotCap (σ k1) <;> cases hc2 : slotCap (σ k2)
    -- `k` a union
    · by_cases h12 : k1 = k2
      · subst h12
        refine nsub k k1 (Ne.symm hk1) fun x hx => ?_
        obtain ⟨i, hi, hxi⟩ := (mem_slotSet_cup A _ hc x).1 hx
        exact (mem_slotSet_cup A _ hc1 x).2 ⟨i, (hcov i hi).elim id id, hxi⟩
      · refine n3cup k1 k2 k h12 hk1 hk2 fun x hx => ?_
        obtain ⟨i, hi, hxi⟩ := (mem_slotSet_cup A _ hc x).1 hx
        rcases hcov i hi with h | h
        · exact Or.inl ((mem_slotSet_cup A _ hc1 x).2 ⟨i, h, hxi⟩)
        · exact Or.inr ((mem_slotSet_cup A _ hc2 x).2 ⟨i, h, hxi⟩)
    · refine nsub k2 k hk2 fun x hx => ?_
      exact (mem_slotSet_cup A _ hc x).2 ⟨b, hb, (mem_slotSet_cap A _ hc2 x).1 hx b hb2⟩
    · refine nsub k1 k hk1 fun x hx => ?_
      exact (mem_slotSet_cup A _ hc x).2 ⟨a, ha, (mem_slotSet_cap A _ hc1 x).1 hx a ha1⟩
    · refine nsub k1 k hk1 fun x hx => ?_
      exact (mem_slotSet_cup A _ hc x).2 ⟨a, ha, (mem_slotSet_cap A _ hc1 x).1 hx a ha1⟩
    -- `k` an intersection
    · refine nsub k k1 (Ne.symm hk1) fun x hx => ?_
      exact (mem_slotSet_cup A _ hc1 x).2 ⟨a, ha1, (mem_slotSet_cap A _ hc x).1 hx a ha⟩
    · refine nsub k k1 (Ne.symm hk1) fun x hx => ?_
      exact (mem_slotSet_cup A _ hc1 x).2 ⟨a, ha1, (mem_slotSet_cap A _ hc x).1 hx a ha⟩
    · refine nsub k k2 (Ne.symm hk2) fun x hx => ?_
      exact (mem_slotSet_cup A _ hc2 x).2 ⟨b, hb2, (mem_slotSet_cap A _ hc x).1 hx b hb⟩
    · by_cases h12 : k1 = k2
      · subst h12
        refine nsub k1 k hk1 fun x hx => ?_
        refine (mem_slotSet_cap A _ hc x).2 fun i hi => ?_
        exact (mem_slotSet_cap A _ hc1 x).1 hx i ((hcov i hi).elim id id)
      · refine n3cap k1 k2 k h12 hk1 hk2 fun x hx1 hx2 => ?_
        refine (mem_slotSet_cap A _ hc x).2 fun i hi => ?_
        rcases hcov i hi with h | h
        · exact (mem_slotSet_cap A _ hc1 x).1 hx1 i h
        · exact (mem_slotSet_cap A _ hc2 x).1 hx2 i h
  have hcard := card_le_one_of_private (fun k => slotIn (σ k)) hpriv
  intro k
  obtain ⟨i, hi, -⟩ := eq_inl_of_slotIn_card (σ k) (hcard k)
  refine ⟨i, c k, ?_⟩
  have := hσ k
  rw [hi] at this
  exact this

end Parity

end GenusTutte
```

### `ParityGenus.lean`

```lean
import Rigidity

/-!
# The parity gadgets: equal genus-`t` polynomials, different genus-`(t+1)` polynomials (`t = s + 4`)

Equality: tuples with `Miss ≠ ∅` are matched by the flip `τ_{pick Miss}` (`sum_miss_eq`); tuples with
`Miss = ∅` are, by the rigidity lemma, exactly the permutation patterns `A i = S p (π i) (c i)` and are
matched by keeping `(π, c)`. Separation: the witness `(S 0 0 1, …, S 0 (t-1) 1, {0})` exists only on the
even side.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace GenusTutte

namespace Parity

variable (s : ℕ)

/-! ## Bad families and the flip transfer -/

/-- `k`-bad sets: the two half-spaces of coordinate `k`. -/
def Bad (p : ZMod 2) (k : Fin (s + 4)) (B : Finset (E (s + 4) p)) : Prop := ∃ c, B = S p k c

theorem H1 (j k : Fin (s + 4)) (B : Finset (E (s + 4) 0)) :
    Bad s 1 k (B.map (tau j).toEmbedding) ↔ Bad s 0 k B := by
  constructor
  · rintro ⟨c, hc⟩
    have := congrArg (fun C => C.map (tau j).symm.toEmbedding) hc
    simp only [Finset.map_map] at this
    rw [show ((tau j).toEmbedding.trans (tau j).symm.toEmbedding) = Function.Embedding.refl _ by
      ext; simp, Finset.map_refl, map_tau_symm_S] at this
    exact ⟨_, this⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, map_tau_S s j k c⟩

theorem map_eq_S_one {k m : Fin (s + 4)} {B : Finset (E (s + 4) 0)} {c : Bool}
    (h : B.map (tau k).toEmbedding = S 1 m c) : B = S 0 m (if m = k then !c else c) := by
  have := congrArg (fun C => C.map (tau k).symm.toEmbedding) h
  simp only [Finset.map_map] at this
  rwa [show ((tau k).toEmbedding.trans (tau k).symm.toEmbedding) = Function.Embedding.refl _ by
    ext; simp, Finset.map_refl, map_tau_symm_S] at this

theorem H2 (k : Fin (s + 4)) (B : Finset (E (s + 4) 0)) (hB : ¬ Bad s 0 k B) :
    (gadget s 1).rank (B.map (tau k).toEmbedding) = (gadget s 0).rank B := by
  unfold Gadget.rank
  rw [card_map]
  congr 2
  apply propext
  rw [mem_gadget_H, mem_gadget_H]
  constructor
  · rintro ⟨m, hm⟩
    have := map_eq_S_one s hm
    by_cases hmk : m = k
    · exact absurd ⟨_, hmk ▸ this⟩ hB
    · rw [if_neg' hmk] at this; exact ⟨m, this⟩
  · rintro ⟨m, rfl⟩
    have hmk : m ≠ k := fun h => hB ⟨true, h ▸ rfl⟩
    refine ⟨m, ?_⟩
    rw [map_tau_S, if_neg' hmk]

/-! ## Permutation patterns -/

/-- The pattern tuple `i ↦ S p (π i) (c i)`. -/
def pat (p : ZMod 2) (π : Fin (s + 4) → Fin (s + 4)) (c : Fin (s + 4) → Bool) :
    Fin (s + 4) → Finset (E (s + 4) p) := fun i => S p (π i) (c i)

theorem pat_stats (p : ZMod 2) (π : Fin (s + 4) → Fin (s + 4)) (hπ : Function.Injective π)
    (c : Fin (s + 4) → Bool) (σ : Slot (s + 4)) :
    (slotSet (pat s p π c) σ).card =
        (match σ with
          | Sum.inl _ => 2 ^ (s + 2)
          | Sum.inr (_, false) => 2 ^ (s + 1)
          | Sum.inr (_, true) => 3 * 2 ^ (s + 1)) ∧
      (slotSet (pat s p π c) σ ∈ (gadget s p).H ↔
        (match σ with
          | Sum.inl i => c i = true
          | Sum.inr _ => False)) := by
  have e : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := pow_succ 2 (s + 1)
  have := Nat.one_le_two_pow (n := s + 1)
  rcases σ with i | ⟨q, b⟩
  · exact ⟨card_S s p _ _, S_mem_H_iff s p _ _⟩
  · have hq : π q.1.1 ≠ π q.1.2 := fun h => absurd (hπ h) (ne_of_lt q.2)
    cases b
    · have hc := card_S_inter s p _ _ hq (c q.1.1) (c q.1.2)
      refine ⟨hc, ?_⟩
      simp only [iff_false]
      exact not_mem_H_of_card s p _ (by simp only [slotSet, pat]; omega)
    · have hc := card_S_union s p _ _ hq (c q.1.1) (c q.1.2)
      refine ⟨hc, ?_⟩
      simp only [iff_false]
      exact not_mem_H_of_card s p _ (by simp only [slotSet, pat]; omega)

theorem pat_rank (π : Fin (s + 4) → Fin (s + 4)) (hπ : Function.Injective π)
    (c : Fin (s + 4) → Bool) (σ : Slot (s + 4)) :
    (slotSet (pat s 1 π c) σ).card = (slotSet (pat s 0 π c) σ).card ∧
      (gadget s 1).rank (slotSet (pat s 1 π c) σ) = (gadget s 0).rank (slotSet (pat s 0 π c) σ) := by
  obtain ⟨c1, m1⟩ := pat_stats s 1 π hπ c σ
  obtain ⟨c0, m0⟩ := pat_stats s 0 π hπ c σ
  refine ⟨c1.trans c0.symm, ?_⟩
  unfold Gadget.rank
  rw [c1, c0]
  congr 2
  exact propext (m1.trans m0.symm)

/-- Tuples all of whose coordinates are hit form exactly the permutation patterns. -/
theorem pattern_of_hit (p : ZMod 2) (A : Fin (s + 4) → Finset (E (s + 4) p))
    (hA : ∀ k, ∃ σ : Slot (s + 4), ∃ c, slotSet A σ = S p k c) :
    ∃ π c, Function.Injective π ∧ A = pat s p π c := by
  have hr := rigidity s p A hA
  choose f cf hf using hr
  have finj : Function.Injective f := by
    intro k k' hkk
    have h1 := hf k
    have h2 := hf k'
    rw [hkk, h2] at h1
    exact (S_inj s p h1).1.symm
  have fsurj := Finite.injective_iff_surjective.1 finj
  let g := Function.surjInv fsurj
  have hfg : ∀ i, f (g i) = i := Function.surjInv_eq fsurj
  refine ⟨g, fun i => cf (g i), Function.injective_surjInv fsurj, ?_⟩
  funext i
  show A i = S p (g i) (cf (g i))
  rw [← hf (g i), hfg]

theorem hit_of_pattern (p : ZMod 2) (π : Fin (s + 4) → Fin (s + 4)) (hπ : Function.Injective π)
    (c : Fin (s + 4) → Bool) : ∀ k, ∃ σ : Slot (s + 4), Bad s p k (slotSet (pat s p π c) σ) := by
  intro k
  obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.1 hπ) k
  exact ⟨Sum.inl i, c i, rfl⟩

/-- Decoding a half-space. -/
noncomputable def code (p : ZMod 2) : Finset (E (s + 4) p) → Fin (s + 4) × Bool :=
  Function.invFun fun kc : Fin (s + 4) × Bool => S p kc.1 kc.2

theorem code_S (p : ZMod 2) (k : Fin (s + 4)) (c : Bool) : code s p (S p k c) = (k, c) := by
  have hinj : Function.Injective fun kc : Fin (s + 4) × Bool => S p kc.1 kc.2 := by
    rintro ⟨k, c⟩ ⟨k', c'⟩ h
    obtain ⟨h1, h2⟩ := S_inj s p h
    exact Prod.ext h1 h2
  exact Function.leftInverse_invFun hinj (k, c)

/-- Re-encode a tuple on the other parity class. -/
noncomputable def recode (p q : ZMod 2) (A : Fin (s + 4) → Finset (E (s + 4) p)) :
    Fin (s + 4) → Finset (E (s + 4) q) := fun i => S q (code s p (A i)).1 (code s p (A i)).2

theorem recode_pat (p q : ZMod 2) (π : Fin (s + 4) → Fin (s + 4)) (c : Fin (s + 4) → Bool) :
    recode s p q (pat s p π c) = pat s q π c := by
  funext i
  simp [recode, pat, code_S]

theorem not_nonempty_miss_iff (p : ZMod 2) (A : Fin (s + 4) → Finset (E (s + 4) p)) :
    ¬ (miss (m := s + 3) (Bad s p) A).Nonempty ↔ ∀ k, ∃ σ : Slot (s + 4), Bad s p k (slotSet A σ) := by
  rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem]
  refine forall_congr' fun k => ?_
  rw [mem_miss]
  push Not
  rfl

/-- **Equality of the genus-`t` polynomials of the two parity gadgets.** -/
theorem gt_eq :
    gt (s + 4) (gadget s 0).rank ((gadget s 0).rank univ) =
      gt (s + 4) (gadget s 1).rank ((gadget s 1).rank univ) := by
  rw [gadget_rank_univ, gadget_rank_univ]
  unfold gt
  rw [← Finset.sum_filter_add_sum_filter_not univ
      (fun A => (miss (m := s + 3) (Bad s 0) A).Nonempty),
    ← Finset.sum_filter_add_sum_filter_not univ
      (fun A => (miss (m := s + 3) (Bad s 1) A).Nonempty)]
  congr 1
  · exact sum_miss_eq (m := s + 3) _ _ _ (tau (t := s + 4)) (Bad s 0) (Bad s 1) (H1 s) (H2 s)
  · refine Finset.sum_nbij' (recode s 0 1) (recode s 1 0) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      simp only [mem_filter, mem_univ, true_and, not_nonempty_miss_iff] at hA ⊢
      obtain ⟨π, c, hπ, rfl⟩ := pattern_of_hit s 0 A (fun k => by
        obtain ⟨σ, c, hc⟩ := hA k; exact ⟨σ, c, hc⟩)
      rw [recode_pat]
      exact hit_of_pattern s 1 π hπ c
    · intro A hA
      simp only [mem_filter, mem_univ, true_and, not_nonempty_miss_iff] at hA ⊢
      obtain ⟨π, c, hπ, rfl⟩ := pattern_of_hit s 1 A (fun k => by
        obtain ⟨σ, c, hc⟩ := hA k; exact ⟨σ, c, hc⟩)
      rw [recode_pat]
      exact hit_of_pattern s 0 π hπ c
    · intro A hA
      simp only [mem_filter, mem_univ, true_and, not_nonempty_miss_iff] at hA
      obtain ⟨π, c, hπ, rfl⟩ := pattern_of_hit s 0 A (fun k => by
        obtain ⟨σ, c, hc⟩ := hA k; exact ⟨σ, c, hc⟩)
      rw [recode_pat, recode_pat]
    · intro A hA
      simp only [mem_filter, mem_univ, true_and, not_nonempty_miss_iff] at hA
      obtain ⟨π, c, hπ, rfl⟩ := pattern_of_hit s 1 A (fun k => by
        obtain ⟨σ, c, hc⟩ := hA k; exact ⟨σ, c, hc⟩)
      rw [recode_pat, recode_pat]
    · intro A hA
      simp only [mem_filter, mem_univ, true_and, not_nonempty_miss_iff] at hA
      obtain ⟨π, c, hπ, rfl⟩ := pattern_of_hit s 0 A (fun k => by
        obtain ⟨σ, c, hc⟩ := hA k; exact ⟨σ, c, hc⟩)
      rw [recode_pat]
      symm
      exact term_congr _ _ _ _ _ _ (fun σ => (pat_rank s π hπ c σ).1)
        (fun σ => (pat_rank s π hπ c σ).2)

/-! ## Separation at genus `t + 1` -/

/-- The zero vector, which is even. -/
def zero : E (s + 4) 0 := ⟨fun _ => false, by simp [par]⟩

/-- The separating tuple on the even side. -/
def witness : Fin (s + 5) → Finset (E (s + 4) 0) := fun j =>
  if h : (j : ℕ) < s + 4 then S 0 ⟨j, h⟩ true else {zero s}

theorem witness_castSucc (k : Fin (s + 4)) : witness s (Fin.castSucc k) = S 0 k true := by
  simp [witness]

theorem witness_last : witness s (Fin.last (s + 4)) = {zero s} := by
  simp [witness]

/-- **The genus-`(t+1)` polynomials differ.** -/
theorem gt_ne :
    gt (s + 5) (gadget s 0).rank ((gadget s 0).rank univ) ≠
      gt (s + 5) (gadget s 1).rank ((gadget s 1).rank univ) := by
  rw [gadget_rank_univ, gadget_rank_univ]
  have e : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := pow_succ 2 (s + 1)
  have hpos := Nat.one_le_two_pow (n := s + 1)
  refine gt_ne_of_witness _ _ _ (gadget s 0).rank_le_r (gadget s 0).rank_le_card
    (gadget s 1).rank_le_r (gadget s 1).rank_le_card (witness s) ?_
  intro A hA
  -- the first `t` probes are circuit-hyperplanes of the odd gadget
  have hH : ∀ k : Fin (s + 4), ∃ m, A (Fin.castSucc k) = S 1 m true := by
    intro k
    obtain ⟨hc, hr⟩ := hA (Sum.inl (Fin.castSucc k))
    simp only [slotSet, witness_castSucc] at hc hr
    rw [card_S] at hc
    have h0 : (gadget s 0).rank (S 0 k true) = 2 ^ (s + 2) - 1 := by
      unfold Gadget.rank
      rw [card_S, if_pos' ((S_mem_H_iff s 0 k true).2 rfl)]
      show min (2 ^ (s + 2)) (2 ^ (s + 2)) - 1 = _
      rw [min_self]
    rw [h0] at hr
    by_contra hcon
    have hn : A (Fin.castSucc k) ∉ (gadget s 1).H := by
      rw [mem_gadget_H]; push Not; intro m hm; exact hcon ⟨m, hm⟩
    unfold Gadget.rank at hr
    rw [if_neg' hn, hc] at hr
    change min (2 ^ (s + 2)) (2 ^ (s + 2)) - 0 = 2 ^ (s + 2) - 1 at hr
    omega
  choose f hf using hH
  have finj : Function.Injective f := by
    have key : ∀ k k' : Fin (s + 4), k < k' → f k ≠ f k' := by
      intro k k' hlt hEq
      have hlt' : Fin.castSucc k < Fin.castSucc k' := Fin.castSucc_lt_castSucc_iff.2 hlt
      obtain ⟨hc, -⟩ := hA (Sum.inr (⟨(Fin.castSucc k, Fin.castSucc k'), hlt'⟩, false))
      simp only [slotSet, witness_castSucc, hf, hEq, inter_self] at hc
      rw [card_S, card_S_inter s 0 k k' (ne_of_lt hlt)] at hc
      omega
    intro k k' hEq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key k k' h hEq
    · exact key k' k h hEq.symm
  have fsurj := Finite.injective_iff_surjective.1 finj
  -- the last probe has one element, which lies in some half-space
  obtain ⟨hc, -⟩ := hA (Sum.inl (Fin.last (s + 4)))
  simp only [slotSet, witness_last, card_singleton] at hc
  obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < (A (Fin.last (s + 4))).card)
  obtain ⟨k0, hk0⟩ : ∃ k0, x.1 k0 = true := by
    by_contra hcon
    push Not at hcon
    have : x.1 = fun _ => false := funext fun k => by simpa using hcon k
    have hp := x.2
    rw [this] at hp
    simp [par] at hp
    exact absurd hp (by decide)
  obtain ⟨k, rfl⟩ := fsurj k0
  have hlt : Fin.castSucc k < Fin.last (s + 4) := Fin.castSucc_lt_last k
  obtain ⟨hc2, -⟩ := hA (Sum.inr (⟨(Fin.castSucc k, Fin.last (s + 4)), hlt⟩, false))
  simp only [slotSet, witness_castSucc, witness_last] at hc2
  have hz : S 0 k true ∩ {zero s} = ∅ := by
    ext y
    simp only [mem_inter, mem_S, mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro h rfl
    simp [zero] at h
  rw [hz, card_empty] at hc2
  have : x ∈ A (Fin.castSucc k) ∩ A (Fin.last (s + 4)) :=
    mem_inter.2 ⟨by rw [hf]; exact mem_S.2 hk0, hx⟩
  rw [card_eq_zero.1 hc2] at this
  exact Finset.notMem_empty x this

/-- The two parity gadgets have the same size. -/
noncomputable def equivFin (p : ZMod 2) : E (s + 4) p ≃ Fin (2 ^ (s + 3)) :=
  Fintype.equivFinOfCardEq (by rw [← Finset.card_univ, card_E])

/-- **The conjecture for every genus `g ≥ 4`.** -/
theorem conj_ge_four : MiezakiConj512 (s + 4) :=
  conj_of_gadgets (gadget s 0) (gadget s 1) (equivFin s 0) (equivFin s 1) (gt_eq s) (gt_ne s)

end Parity

end GenusTutte
```

### `LowGenus.lean`

```lean
import GTPad

/-!
# Shared tools for the low genera `g = 1, 2, 3`

* Formal Boolean evaluation of slots and a chain cover of `Slot h` (`h ≤ 3`) by `h` chains of the
  pointwise order. Hence `h + 1` pairwise incomparable slot sets are impossible, so if `h + 1` disjoint
  families of equal-size sets are given, every `h`-tuple misses one family (`miss_nonempty_of_chains`).
* `low_eq`: two gadgets on the same finite type with ground permutations `φ k` and bad families `Bad k`
  satisfying finitely checkable conditions have equal genus-`h` polynomials.
* `mem_H_of_rank`: a 3-set of rank 2 in a rank-3 gadget is a circuit-hyperplane.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace GenusTutte

/-- Formal Boolean function of a slot. -/
def feval {h : ℕ} : Slot h → (Fin h → Bool) → Bool
  | Sum.inl i, v => v i
  | Sum.inr (q, false), v => v q.1.1 && v q.1.2
  | Sum.inr (q, true), v => v q.1.1 || v q.1.2

theorem mem_slotSet_iff_feval {α : Type*} [DecidableEq α] {h : ℕ} (A : Fin h → Finset α)
    (σ : Slot h) (x : α) : x ∈ slotSet A σ ↔ feval σ (fun i => decide (x ∈ A i)) = true := by
  rcases σ with i | ⟨q, b⟩
  · simp [slotSet, feval]
  · cases b <;> simp [slotSet, feval]

/-- Formal pointwise order of slots. -/
def fle {h : ℕ} (σ σ' : Slot h) : Prop := ∀ v : Fin h → Bool, feval σ v = true → feval σ' v = true

instance {h : ℕ} (σ σ' : Slot h) : Decidable (fle σ σ') := by unfold fle; infer_instance

theorem slotSet_subset_of_fle {α : Type*} [DecidableEq α] {h : ℕ} (A : Fin h → Finset α)
    {σ σ' : Slot h} (hle : fle σ σ') : slotSet A σ ⊆ slotSet A σ' := by
  intro x hx
  rw [mem_slotSet_iff_feval] at hx ⊢
  exact hle _ hx

/-- If `Slot h` is covered by `h` chains, an `h`-tuple misses one of `h + 1` disjoint families of
equal-size sets. -/
theorem miss_nonempty_of_chains {α : Type*} [Fintype α] [DecidableEq α] {h c : ℕ} (ch : Slot h → Fin h)
    (hch : ∀ σ σ', ch σ = ch σ' → fle σ σ' ∨ fle σ' σ)
    (Bad : Fin (h + 1) → Finset (Finset α))
    (hdisj : ∀ k k' : Fin (h + 1), ∀ B ∈ Bad k, B ∈ Bad k' → k = k')
    (hcard : ∀ k : Fin (h + 1), ∀ B ∈ Bad k, B.card = c) (A : Fin h → Finset α) :
    (miss (m := h) (fun k B => B ∈ Bad k) A).Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at hcon
  have hit : ∀ k, ∃ σ, slotSet A σ ∈ Bad k := by
    intro k
    have := hcon k
    rw [mem_miss] at this
    push Not at this
    exact this
  choose σ hσ using hit
  obtain ⟨k, k', hne, hk⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k => ch (σ k)) (by simp)
  have heq : slotSet A (σ k) = slotSet A (σ k') := by
    rcases hch _ _ hk with hle | hle
    · exact eq_of_subset_of_card_le (slotSet_subset_of_fle A hle)
        (by rw [hcard _ _ (hσ k), hcard _ _ (hσ k')])
    · exact (eq_of_subset_of_card_le (slotSet_subset_of_fle A hle)
        (by rw [hcard _ _ (hσ k), hcard _ _ (hσ k')])).symm
  exact hne (hdisj k k' _ (hσ k) (heq ▸ hσ k'))

/-! ## Chain covers for `h = 1, 2, 3` -/

def ch1 : Slot 1 → Fin 1 := fun _ => 0

theorem ch1_spec : ∀ σ σ' : Slot 1, ch1 σ = ch1 σ' → fle σ σ' ∨ fle σ' σ := by decide

def ch2 : Slot 2 → Fin 2
  | Sum.inl i => i
  | Sum.inr _ => 0

theorem ch2_spec : ∀ σ σ' : Slot 2, ch2 σ = ch2 σ' → fle σ σ' ∨ fle σ' σ := by decide

/-- Chains `a₀∧a₁ ≤ a₀ ≤ a₀∨a₂`, `a₁∧a₂ ≤ a₁ ≤ a₀∨a₁`, `a₀∧a₂ ≤ a₂ ≤ a₁∨a₂`. -/
def ch3 : Slot 3 → Fin 3
  | Sum.inl i => i
  | Sum.inr (q, false) =>
      if (q.1.1 : ℕ) + q.1.2 = 1 then 0 else if (q.1.1 : ℕ) + q.1.2 = 3 then 1 else 2
  | Sum.inr (q, true) =>
      if (q.1.1 : ℕ) + q.1.2 = 2 then 0 else if (q.1.1 : ℕ) + q.1.2 = 1 then 1 else 2

theorem ch3_spec : ∀ σ σ' : Slot 3, ch3 σ = ch3 σ' → fle σ σ' ∨ fle σ' σ := by decide

/-! ## Equality from finitely checkable data -/

theorem low_eq {n h : ℕ} (GX GY : Gadget (Fin n)) (Bad : Fin (h + 1) → Finset (Finset (Fin n)))
    (φ : Fin (h + 1) → Equiv.Perm (Fin n))
    (d1 : ∀ j k, (Bad k).image (fun B => B.map (φ j).toEmbedding) = Bad k)
    (d2 : ∀ k, (GX.H \ Bad k).image (fun B => B.map (φ k).toEmbedding) = GY.H \ Bad k)
    (hmiss : ∀ A : Fin h → Finset (Fin n), (miss (m := h) (fun k B => B ∈ Bad k) A).Nonempty)
    (hr : GY.r = GX.r) (hR : GX.rank univ = GY.rank univ) :
    gt h GX.rank (GX.rank univ) = gt h GY.rank (GY.rank univ) := by
  have H1 : ∀ j k (B : Finset (Fin n)), B.map (φ j).toEmbedding ∈ Bad k ↔ B ∈ Bad k := by
    intro j k B
    constructor
    · intro hB
      rw [← d1 j k, mem_image] at hB
      obtain ⟨B', hB', hEq⟩ := hB
      rwa [← map_inj.1 hEq]
    · intro hB
      rw [← d1 j k]
      exact mem_image_of_mem _ hB
  have H2 : ∀ k (B : Finset (Fin n)), B ∉ Bad k →
      GY.rank (B.map (φ k).toEmbedding) = GX.rank B := by
    intro k B hB
    unfold Gadget.rank
    rw [card_map, hr]
    congr 2
    apply propext
    constructor
    · intro hY
      have : B.map (φ k).toEmbedding ∈ GY.H \ Bad k := mem_sdiff.2 ⟨hY, fun h' => hB ((H1 k k B).1 h')⟩
      rw [← d2 k, mem_image] at this
      obtain ⟨B', hB', hEq⟩ := this
      rw [← map_inj.1 hEq]
      exact (mem_sdiff.1 hB').1
    · intro hX
      have : B.map (φ k).toEmbedding ∈ GY.H \ Bad k := by
        rw [← d2 k]; exact mem_image_of_mem _ (mem_sdiff.2 ⟨hX, hB⟩)
      exact (mem_sdiff.1 this).1
  rw [← hR]
  unfold gt
  have e1 : (univ : Finset (Fin h → Finset (Fin n))) =
      univ.filter fun A => (miss (m := h) (fun k B => B ∈ Bad k) A).Nonempty := by
    ext A; simp [hmiss A]
  rw [e1]
  exact sum_miss_eq (m := h) _ _ _ φ (fun k B => B ∈ Bad k) (fun k B => B ∈ Bad k) H1 H2

theorem mem_H_of_rank {α : Type*} [Fintype α] [DecidableEq α] (G : Gadget α) (hr : G.r = 3)
    (B : Finset α) (hc : B.card = 3) (hrk : G.rank B = 2) : B ∈ G.H := by
  by_contra hn
  unfold Gadget.rank at hrk
  rw [if_neg' hn, hc, hr] at hrk
  simp at hrk

end GenusTutte

/-! ## Indexed families (keeps every `decide` over `Fin` indices) -/

namespace GenusTutte

/-- A rank-3 gadget whose circuit-hyperplanes are an indexed family of 3-sets. -/
def Gadget.ofFamily {n a : ℕ} (T : Fin a → Finset (Fin n)) (hc : ∀ i, (T i).card = 3)
    (hi : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) : Gadget (Fin n) where
  r := 3
  H := univ.image T
  hr := by norm_num
  hcard := by
    intro B hB
    obtain ⟨i, -, rfl⟩ := mem_image.1 hB
    exact hc i
  hinter := by
    intro B hB B' hB' hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hB
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB'
    have := hi i j fun h' => hne (h' ▸ rfl)
    omega

theorem Gadget.rank_univ_of_lt {α : Type*} [Fintype α] [DecidableEq α] (G : Gadget α)
    (hlt : G.r < Fintype.card α) : G.rank univ = G.r := by
  have hn : (univ : Finset α) ∉ G.H := fun h' => by
    have := G.hcard _ h'
    rw [card_univ] at this
    omega
  unfold Gadget.rank
  rw [if_neg' hn, card_univ]
  omega

theorem Gadget.rank_of_mem {α : Type*} [Fintype α] [DecidableEq α] (G : Gadget α)
    {B : Finset α} (hB : B ∈ G.H) : G.rank B = G.r - 1 := by
  unfold Gadget.rank
  rw [if_pos' hB, G.hcard B hB, min_self]

/-- Equality for indexed low-genus data. -/
theorem low_eq_idx {n h a b : ℕ} (TX TY : Fin a → Finset (Fin n))
    (hcX : ∀ i, (TX i).card = 3) (hiX : ∀ i j, i ≠ j → (TX i ∩ TX j).card ≤ 1)
    (hcY : ∀ i, (TY i).card = 3) (hiY : ∀ i j, i ≠ j → (TY i ∩ TY j).card ≤ 1)
    (BadT : Fin (h + 1) → Fin b → Finset (Fin n)) (φ : Fin (h + 1) → Equiv.Perm (Fin n))
    (e1 : ∀ j k l, ∃ l', (BadT k l).map (φ j).toEmbedding = BadT k l')
    (e2 : ∀ j k l', ∃ l, (BadT k l).map (φ j).toEmbedding = BadT k l')
    (e3 : ∀ k i, (∀ l, TX i ≠ BadT k l) → ∃ i', (TX i).map (φ k).toEmbedding = TY i')
    (e4 : ∀ k i', (∀ l, TY i' ≠ BadT k l) → ∃ i, (TX i).map (φ k).toEmbedding = TY i')
    (e5 : ∀ k k' l l', BadT k l = BadT k' l' → k = k')
    (e6 : ∀ k l, (BadT k l).card = 3)
    (ch : Slot h → Fin h) (hch : ∀ σ σ', ch σ = ch σ' → fle σ σ' ∨ fle σ' σ) (hn : 3 < n) :
    gt h (Gadget.ofFamily TX hcX hiX).rank ((Gadget.ofFamily TX hcX hiX).rank univ) =
      gt h (Gadget.ofFamily TY hcY hiY).rank ((Gadget.ofFamily TY hcY hiY).rank univ) := by
  set GX := Gadget.ofFamily TX hcX hiX
  set GY := Gadget.ofFamily TY hcY hiY
  let Bad : Fin (h + 1) → Finset (Finset (Fin n)) := fun k => univ.image (BadT k)
  have memBad : ∀ k B, B ∈ Bad k ↔ ∃ l, B = BadT k l := by
    intro k B; simp [Bad, eq_comm]
  have memX : ∀ B, B ∈ GX.H ↔ ∃ i, B = TX i := by
    intro B; simp [GX, Gadget.ofFamily, eq_comm]
  have memY : ∀ B, B ∈ GY.H ↔ ∃ i, B = TY i := by
    intro B; simp [GY, Gadget.ofFamily, eq_comm]
  have H1 : ∀ j k (B : Finset (Fin n)), B.map (φ j).toEmbedding ∈ Bad k ↔ B ∈ Bad k := by
    intro j k B
    rw [memBad, memBad]
    constructor
    · rintro ⟨l', hl'⟩
      obtain ⟨l, hl⟩ := e2 j k l'
      exact ⟨l, map_inj.1 (hl'.trans hl.symm)⟩
    · rintro ⟨l, rfl⟩
      obtain ⟨l', hl'⟩ := e1 j k l
      exact ⟨l', hl'⟩
  have H2 : ∀ k (B : Finset (Fin n)), B ∉ Bad k →
      GY.rank (B.map (φ k).toEmbedding) = GX.rank B := by
    intro k B hB
    unfold Gadget.rank
    rw [card_map]
    show min 3 _ - _ = min 3 _ - _
    congr 2
    apply propext
    rw [memX, memY]
    constructor
    · rintro ⟨i', hi'⟩
      have hY : ∀ l, TY i' ≠ BadT k l := by
        intro l hl
        apply hB
        rw [← H1 k k B, memBad]
        exact ⟨l, hi'.trans hl⟩
      obtain ⟨i, hi⟩ := e4 k i' hY
      exact ⟨i, map_inj.1 (hi'.trans hi.symm)⟩
    · rintro ⟨i, rfl⟩
      have hX : ∀ l, TX i ≠ BadT k l := fun l hl => hB ((memBad k _).2 ⟨l, hl⟩)
      obtain ⟨i', hi'⟩ := e3 k i hX
      exact ⟨i', hi'⟩
  have hmiss : ∀ A : Fin h → Finset (Fin n), (miss (m := h) (fun k B => B ∈ Bad k) A).Nonempty :=
    miss_nonempty_of_chains (c := 3) ch hch Bad
      (by
        intro k k' B hB hB'
        obtain ⟨l, rfl⟩ := (memBad k B).1 hB
        obtain ⟨l', hl'⟩ := (memBad k' _).1 hB'
        exact e5 k k' l l' hl')
      (by
        intro k B hB
        obtain ⟨l, rfl⟩ := (memBad k B).1 hB
        exact e6 k l)
  have hRX : GX.rank univ = 3 := GX.rank_univ_of_lt (by simpa [GX, Gadget.ofFamily] using hn)
  have hRY : GY.rank univ = 3 := GY.rank_univ_of_lt (by simpa [GY, Gadget.ofFamily] using hn)
  rw [hRX, hRY]
  unfold gt
  have e : (univ : Finset (Fin h → Finset (Fin n))) =
      univ.filter fun A => (miss (m := h) (fun k B => B ∈ Bad k) A).Nonempty := by
    ext A; simp [hmiss A]
  rw [e]
  exact sum_miss_eq (m := h) _ _ _ φ (fun k B => B ∈ Bad k) (fun k B => B ∈ Bad k) H1 H2

end GenusTutte
```

### `Low1.lean`

```lean
import LowGenus

/-!
# Genus 1 (PROOF-361823 §5, `g = 1`)

Rank 3 on six elements with two circuit-hyperplanes: disjoint (`{0,1,2}, {3,4,5}`) versus meeting in one
element (`{0,1,2}, {2,3,4}`). Equality at genus 1 by the bijection with `φ = id, swap 2 5`; at genus 2 the
two singleton probes can be disjoint circuit-hyperplanes only in the first matroid.
-/

open Finset

namespace GenusTutte

namespace Low1

def GX : Gadget (Fin 6) where
  r := 3
  H := {{0, 1, 2}, {3, 4, 5}}
  hr := by decide +kernel
  hcard := by decide +kernel
  hinter := by decide +kernel

def GY : Gadget (Fin 6) where
  r := 3
  H := {{0, 1, 2}, {2, 3, 4}}
  hr := by decide +kernel
  hcard := by decide +kernel
  hinter := by decide +kernel

def Bad : Fin 2 → Finset (Finset (Fin 6)) := ![{{3, 4, 5}, {2, 3, 4}}, {{0, 1, 2}, {0, 1, 5}}]

def φ : Fin 2 → Equiv.Perm (Fin 6) := ![Equiv.refl _, Equiv.swap 2 5]

theorem gt_eq : gt 1 GX.rank (GX.rank univ) = gt 1 GY.rank (GY.rank univ) :=
  low_eq GX GY Bad φ (by decide +kernel) (by decide +kernel)
    (miss_nonempty_of_chains (c := 3) ch1 ch1_spec Bad (by decide +kernel) (by decide +kernel)) rfl (by decide +kernel)

def witness : Fin 2 → Finset (Fin 6) := ![{0, 1, 2}, {3, 4, 5}]

theorem gt_ne : gt 2 GX.rank (GX.rank univ) ≠ gt 2 GY.rank (GY.rank univ) := by
  have hR : GY.rank univ = GX.rank univ := by decide +kernel
  rw [hR]
  refine gt_ne_of_witness _ _ _ GX.rank_le_r GX.rank_le_card
    (fun B => (GY.rank_le_r B).trans_eq rfl) GY.rank_le_card witness ?_
  intro A hA
  have c0 : (A 0).card = 3 := (hA (Sum.inl 0)).1.trans (by decide +kernel)
  have r0 : GY.rank (A 0) = 2 := (hA (Sum.inl 0)).2.trans (by decide +kernel)
  have c1 : (A 1).card = 3 := (hA (Sum.inl 1)).1.trans (by decide +kernel)
  have r1 : GY.rank (A 1) = 2 := (hA (Sum.inl 1)).2.trans (by decide +kernel)
  have i01 : (A 0 ∩ A 1).card = 0 :=
    (hA (Sum.inr (⟨((0 : Fin 2), (1 : Fin 2)), by decide +kernel⟩, false))).1.trans (by decide +kernel)
  have m0 := mem_H_of_rank GY rfl _ c0 r0
  have m1 := mem_H_of_rank GY rfl _ c1 r1
  have key : ∀ B ∈ GY.H, ∀ B' ∈ GY.H, (B ∩ B').card ≠ 0 := by decide +kernel
  exact key _ m0 _ m1 i01

/-- **The conjecture for `g = 1`.** -/
theorem conj_one : MiezakiConj512 1 :=
  conj_of_gadgets GX GY (Equiv.refl _) (Equiv.refl _) gt_eq gt_ne

end Low1

end GenusTutte
```

### `Low2.lean`

```lean
import LowGenus

/-!
# Genus 2 (PROOF-361823 §5): one loose 6-cycle versus two loose 3-cycles

Ground set `Fin 12`: cycle elements `c_i = i` and private elements `d_i = 6 + i` (`i < 6`);
circuit-hyperplanes `T_i = {c_i, d_i, c_(i+1)}` (indices mod 6), rank 3 (`TX`). `TY` replaces `T_2`
and `T_5` by `T'_2 = {c_2, d_2, c_0}` and `T'_5 = {c_5, d_5, c_3}`, cutting the
cycle into two loose 3-cycles. `BadT k = (T_k, T_(k+3), T'_k, T'_(k+3))` with `T'_k = {c_k, d_k, c_(k+4)}`,
`T'_(k+3) = {c_(k+3), d_(k+3), c_(k+1)}`; `φ k` swaps the arc between cut `k` and cut `2` across the two
halves (found by `scripts/find_cut_isos.py`, data `cut-isos.json`). Every check is a finite `decide`
over `Fin` indices. Separation at genus 3: the first loose 3-cycle of `TY` is a tuple of 3
circuit-hyperplanes with cyclic intersection pattern, which the loose 6-cycle does not contain.
-/

open Finset

namespace GenusTutte

namespace Low2

def TX : Fin 6 → Finset (Fin 12) := ![{0, 1, 6}, {1, 2, 7}, {2, 3, 8}, {3, 4, 9}, {4, 5, 10}, {0, 5, 11}]

theorem hcX : ∀ i, (TX i).card = 3 := by decide +kernel

theorem hiX : ∀ i j, i ≠ j → (TX i ∩ TX j).card ≤ 1 := by decide +kernel

/-- The rank-3 sparse paving gadget with circuit-hyperplanes `TX`. -/
def GX : Gadget (Fin 12) := Gadget.ofFamily TX hcX hiX

def TY : Fin 6 → Finset (Fin 12) := ![{0, 1, 6}, {1, 2, 7}, {3, 4, 9}, {4, 5, 10}, {0, 2, 8}, {3, 5, 11}]

theorem hcY : ∀ i, (TY i).card = 3 := by decide +kernel

theorem hiY : ∀ i j, i ≠ j → (TY i ∩ TY j).card ≤ 1 := by decide +kernel

/-- The rank-3 sparse paving gadget with circuit-hyperplanes `TY`. -/
def GY : Gadget (Fin 12) := Gadget.ofFamily TY hcY hiY

def BadT : Fin 3 → Fin 4 → Finset (Fin 12) :=
  ![![{0, 1, 6}, {3, 4, 9}, {0, 4, 6}, {1, 3, 9}],
    ![{1, 2, 7}, {4, 5, 10}, {1, 5, 7}, {2, 4, 10}],
    ![{2, 3, 8}, {0, 5, 11}, {0, 2, 8}, {3, 5, 11}]]

def f0 : Fin 12 → Fin 12 := ![0, 4, 5, 3, 1, 2, 6, 10, 11, 9, 7, 8]

theorem f0_inv : Function.Involutive f0 := by
  unfold Function.Involutive; decide +kernel

def f1 : Fin 12 → Fin 12 := ![0, 1, 5, 3, 4, 2, 6, 7, 11, 9, 10, 8]

theorem f1_inv : Function.Involutive f1 := by
  unfold Function.Involutive; decide +kernel

def f2 : Fin 12 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem f2_inv : Function.Involutive f2 := by
  unfold Function.Involutive; decide +kernel

def φ : Fin 3 → Equiv.Perm (Fin 12) :=
  ![f0_inv.toPerm, f1_inv.toPerm, f2_inv.toPerm]

theorem e1 : ∀ j k l, ∃ l', (BadT k l).map (φ j).toEmbedding = BadT k l' := by decide +kernel

theorem e2 : ∀ j k l', ∃ l, (BadT k l).map (φ j).toEmbedding = BadT k l' := by decide +kernel

theorem e3 : ∀ k i, (∀ l, TX i ≠ BadT k l) → ∃ i', (TX i).map (φ k).toEmbedding = TY i' := by
  decide +kernel

theorem e4 : ∀ k i', (∀ l, TY i' ≠ BadT k l) → ∃ i, (TX i).map (φ k).toEmbedding = TY i' := by
  decide +kernel

theorem e5 : ∀ k k' l l', BadT k l = BadT k' l' → k = k' := by decide +kernel

theorem e6 : ∀ k l, (BadT k l).card = 3 := by decide +kernel

theorem gt_eq : gt 2 GX.rank (GX.rank univ) = gt 2 GY.rank (GY.rank univ) :=
  low_eq_idx TX TY hcX hiX hcY hiY BadT φ e1 e2 e3 e4 e5 e6 ch2 ch2_spec (by norm_num)

/-- The separating tuple: the first loose 3-cycle of `TY`. -/
def witness : Fin 3 → Finset (Fin 12) := ![TY 0, TY 1, TY 4]

/-- The loose 6-cycle has no triangle of circuit-hyperplanes. -/
theorem no_triangle : ∀ a b c : Fin 6, ¬ ((TX a ∩ TX b).card = 1 ∧ (TX a ∩ TX c).card = 1 ∧
    (TX b ∩ TX c).card = 1) := by decide +kernel

theorem gt_ne : gt 3 GX.rank (GX.rank univ) ≠ gt 3 GY.rank (GY.rank univ) := by
  have hR : GX.rank univ = GY.rank univ := by
    rw [GX.rank_univ_of_lt (by simp [GX, Gadget.ofFamily]), GY.rank_univ_of_lt (by simp [GY, Gadget.ofFamily])]; rfl
  rw [hR]
  refine Ne.symm (gt_ne_of_witness _ _ _ GY.rank_le_r GY.rank_le_card
    (fun B => (GX.rank_le_r B).trans_eq rfl) GX.rank_le_card witness ?_)
  intro A hA
  have memX : ∀ B, B ∈ GX.H → ∃ a, B = TX a := by
    intro B hB; obtain ⟨a, -, rfl⟩ := mem_image.1 hB; exact ⟨a, rfl⟩
  obtain ⟨a0, ha0⟩ : ∃ a, A 0 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 0)).1.trans (hcY 0))
    ((hA (Sum.inl 0)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 0)))))
  obtain ⟨a1, ha1⟩ : ∃ a, A 1 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 1)).1.trans (hcY 1))
    ((hA (Sum.inl 1)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 1)))))
  obtain ⟨a2, ha2⟩ : ∃ a, A 2 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 2)).1.trans (hcY 4))
    ((hA (Sum.inl 2)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 4)))))
  have i01 : (A 0 ∩ A 1).card = 1 :=
    (hA (Sum.inr (⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 0 ∩ TY 1).card = 1)
  have i02 : (A 0 ∩ A 2).card = 1 :=
    (hA (Sum.inr (⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 0 ∩ TY 4).card = 1)
  have i12 : (A 1 ∩ A 2).card = 1 :=
    (hA (Sum.inr (⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 1 ∩ TY 4).card = 1)
  rw [ha0] at i01 i02
  rw [ha1] at i01 i12
  rw [ha2] at i02 i12
  exact no_triangle a0 a1 a2 ⟨i01, i02, i12⟩

/-- **The conjecture for `g = 2`.** -/
theorem conj_two : MiezakiConj512 2 :=
  conj_of_gadgets GX GY (Equiv.refl _) (Equiv.refl _) gt_eq gt_ne

end Low2

end GenusTutte
```

### `Low3.lean`

```lean
import LowGenus

/-!
# Genus 3 (PROOF-361823 §5): one loose 8-cycle versus two loose 4-cycles

Ground set `Fin 16`: cycle elements `c_i = i` and private elements `d_i = 8 + i` (`i < 8`);
circuit-hyperplanes `T_i = {c_i, d_i, c_(i+1)}` (indices mod 8), rank 3 (`TX`). `TY` replaces `T_3`
and `T_7` by `T'_3 = {c_3, d_3, c_0}` and `T'_7 = {c_7, d_7, c_4}`, cutting the
cycle into two loose 4-cycles. `BadT k = (T_k, T_(k+4), T'_k, T'_(k+4))` with `T'_k = {c_k, d_k, c_(k+5)}`,
`T'_(k+4) = {c_(k+4), d_(k+4), c_(k+1)}`; `φ k` swaps the arc between cut `k` and cut `3` across the two
halves (found by `scripts/find_cut_isos.py`, data `cut-isos.json`). Every check is a finite `decide`
over `Fin` indices. Separation at genus 4: the first loose 4-cycle of `TY` is a tuple of 4
circuit-hyperplanes with cyclic intersection pattern, which the loose 8-cycle does not contain.
-/

open Finset

namespace GenusTutte

namespace Low3

def TX : Fin 8 → Finset (Fin 16) := ![{0, 1, 8}, {1, 2, 9}, {2, 3, 10}, {3, 4, 11}, {4, 5, 12}, {5, 6, 13}, {6, 7, 14}, {0, 7, 15}]

theorem hcX : ∀ i, (TX i).card = 3 := by decide +kernel

theorem hiX : ∀ i j, i ≠ j → (TX i ∩ TX j).card ≤ 1 := by decide +kernel

/-- The rank-3 sparse paving gadget with circuit-hyperplanes `TX`. -/
def GX : Gadget (Fin 16) := Gadget.ofFamily TX hcX hiX

def TY : Fin 8 → Finset (Fin 16) := ![{0, 1, 8}, {1, 2, 9}, {2, 3, 10}, {4, 5, 12}, {5, 6, 13}, {6, 7, 14}, {0, 3, 11}, {4, 7, 15}]

theorem hcY : ∀ i, (TY i).card = 3 := by decide +kernel

theorem hiY : ∀ i j, i ≠ j → (TY i ∩ TY j).card ≤ 1 := by decide +kernel

/-- The rank-3 sparse paving gadget with circuit-hyperplanes `TY`. -/
def GY : Gadget (Fin 16) := Gadget.ofFamily TY hcY hiY

def BadT : Fin 4 → Fin 4 → Finset (Fin 16) :=
  ![![{0, 1, 8}, {4, 5, 12}, {0, 5, 8}, {1, 4, 12}],
    ![{1, 2, 9}, {5, 6, 13}, {1, 6, 9}, {2, 5, 13}],
    ![{2, 3, 10}, {6, 7, 14}, {2, 7, 10}, {3, 6, 14}],
    ![{3, 4, 11}, {0, 7, 15}, {0, 3, 11}, {4, 7, 15}]]

def f0 : Fin 16 → Fin 16 := ![0, 5, 6, 7, 4, 1, 2, 3, 8, 13, 14, 15, 12, 9, 10, 11]

theorem f0_inv : Function.Involutive f0 := by
  unfold Function.Involutive; decide +kernel

def f1 : Fin 16 → Fin 16 := ![0, 1, 6, 7, 4, 5, 2, 3, 8, 9, 14, 15, 12, 13, 10, 11]

theorem f1_inv : Function.Involutive f1 := by
  unfold Function.Involutive; decide +kernel

def f2 : Fin 16 → Fin 16 := ![0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 10, 15, 12, 13, 14, 11]

theorem f2_inv : Function.Involutive f2 := by
  unfold Function.Involutive; decide +kernel

def f3 : Fin 16 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem f3_inv : Function.Involutive f3 := by
  unfold Function.Involutive; decide +kernel

def φ : Fin 4 → Equiv.Perm (Fin 16) :=
  ![f0_inv.toPerm, f1_inv.toPerm, f2_inv.toPerm, f3_inv.toPerm]

theorem e1 : ∀ j k l, ∃ l', (BadT k l).map (φ j).toEmbedding = BadT k l' := by decide +kernel

theorem e2 : ∀ j k l', ∃ l, (BadT k l).map (φ j).toEmbedding = BadT k l' := by decide +kernel

theorem e3 : ∀ k i, (∀ l, TX i ≠ BadT k l) → ∃ i', (TX i).map (φ k).toEmbedding = TY i' := by
  decide +kernel

theorem e4 : ∀ k i', (∀ l, TY i' ≠ BadT k l) → ∃ i, (TX i).map (φ k).toEmbedding = TY i' := by
  decide +kernel

theorem e5 : ∀ k k' l l', BadT k l = BadT k' l' → k = k' := by decide +kernel

theorem e6 : ∀ k l, (BadT k l).card = 3 := by decide +kernel

theorem gt_eq : gt 3 GX.rank (GX.rank univ) = gt 3 GY.rank (GY.rank univ) :=
  low_eq_idx TX TY hcX hiX hcY hiY BadT φ e1 e2 e3 e4 e5 e6 ch3 ch3_spec (by norm_num)

/-- The separating tuple: the first loose 4-cycle of `TY`. -/
def witness : Fin 4 → Finset (Fin 16) := ![TY 0, TY 1, TY 2, TY 6]

theorem inter_card (a b : Fin 8) : (TX a ∩ TX b).card =
    if a = b then 3 else if b = a + 1 ∨ a = b + 1 then 1 else 0 := by
  revert a b; decide +kernel

/-- The loose 8-cycle has no induced 4-cycle of circuit-hyperplanes (index form). -/
theorem no_square_idx : ∀ a b c d : Fin 8,
    ¬ ((if a = b then 3 else if b = a + 1 ∨ a = b + 1 then 1 else 0) = 1 ∧
      (if b = c then 3 else if c = b + 1 ∨ b = c + 1 then 1 else 0) = 1 ∧
      (if c = d then 3 else if d = c + 1 ∨ c = d + 1 then 1 else 0) = 1 ∧
      (if a = d then 3 else if d = a + 1 ∨ a = d + 1 then 1 else 0) = 1 ∧
      (if a = c then 3 else if c = a + 1 ∨ a = c + 1 then 1 else 0) = 0 ∧
      (if b = d then 3 else if d = b + 1 ∨ b = d + 1 then 1 else 0) = 0) := by decide +kernel

theorem no_square (a b c d : Fin 8) : ¬ ((TX a ∩ TX b).card = 1 ∧ (TX b ∩ TX c).card = 1 ∧
    (TX c ∩ TX d).card = 1 ∧ (TX a ∩ TX d).card = 1 ∧ (TX a ∩ TX c).card = 0 ∧
    (TX b ∩ TX d).card = 0) := by
  simp only [inter_card]
  exact no_square_idx a b c d

theorem gt_ne : gt 4 GX.rank (GX.rank univ) ≠ gt 4 GY.rank (GY.rank univ) := by
  have hR : GX.rank univ = GY.rank univ := by
    rw [GX.rank_univ_of_lt (by simp [GX, Gadget.ofFamily]), GY.rank_univ_of_lt (by simp [GY, Gadget.ofFamily])]; rfl
  rw [hR]
  refine Ne.symm (gt_ne_of_witness _ _ _ GY.rank_le_r GY.rank_le_card
    (fun B => (GX.rank_le_r B).trans_eq rfl) GX.rank_le_card witness ?_)
  intro A hA
  have memX : ∀ B, B ∈ GX.H → ∃ a, B = TX a := by
    intro B hB; obtain ⟨a, -, rfl⟩ := mem_image.1 hB; exact ⟨a, rfl⟩
  obtain ⟨a0, ha0⟩ : ∃ a, A 0 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 0)).1.trans (hcY 0))
    ((hA (Sum.inl 0)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 0)))))
  obtain ⟨a1, ha1⟩ : ∃ a, A 1 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 1)).1.trans (hcY 1))
    ((hA (Sum.inl 1)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 1)))))
  obtain ⟨a2, ha2⟩ : ∃ a, A 2 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 2)).1.trans (hcY 2))
    ((hA (Sum.inl 2)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 2)))))
  obtain ⟨a3, ha3⟩ : ∃ a, A 3 = TX a := memX _ (mem_H_of_rank GX rfl _ ((hA (Sum.inl 3)).1.trans (hcY 6))
    ((hA (Sum.inl 3)).2.trans (GY.rank_of_mem (mem_image_of_mem TY (mem_univ 6)))))
  have i01 : (A 0 ∩ A 1).card = 1 :=
    (hA (Sum.inr (⟨((0 : Fin 4), (1 : Fin 4)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 0 ∩ TY 1).card = 1)
  have i02 : (A 0 ∩ A 2).card = 0 :=
    (hA (Sum.inr (⟨((0 : Fin 4), (2 : Fin 4)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 0 ∩ TY 2).card = 0)
  have i03 : (A 0 ∩ A 3).card = 1 :=
    (hA (Sum.inr (⟨((0 : Fin 4), (3 : Fin 4)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 0 ∩ TY 6).card = 1)
  have i12 : (A 1 ∩ A 2).card = 1 :=
    (hA (Sum.inr (⟨((1 : Fin 4), (2 : Fin 4)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 1 ∩ TY 2).card = 1)
  have i13 : (A 1 ∩ A 3).card = 0 :=
    (hA (Sum.inr (⟨((1 : Fin 4), (3 : Fin 4)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 1 ∩ TY 6).card = 0)
  have i23 : (A 2 ∩ A 3).card = 1 :=
    (hA (Sum.inr (⟨((2 : Fin 4), (3 : Fin 4)), by decide⟩, false))).1.trans
      (by decide +kernel : (TY 2 ∩ TY 6).card = 1)
  rw [ha0] at i01 i02 i03
  rw [ha1] at i01 i12 i13
  rw [ha2] at i02 i12 i23
  rw [ha3] at i03 i13 i23
  exact no_square a0 a1 a2 a3 ⟨i01, i12, i23, i03, i02, i13⟩

/-- **The conjecture for `g = 3`.** -/
theorem conj_three : MiezakiConj512 3 :=
  conj_of_gadgets GX GY (Equiv.refl _) (Equiv.refl _) gt_eq gt_ne

end Low3

end GenusTutte
```

### `GTMain.lean`

```lean
import ParityGenus
import Low1
import Low2
import Low3
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fintype.Powerset

/-!
# MathDB 361823: one-step separation of genus Tutte polynomials (Conjecture 5.12)

**Theorem.** For every positive integer `g` there are two infinite sequences of matroids `M_i`, `N_i`
(on ground sets `Fin (n i)` with `n` strictly increasing) with `T^(g)(M_i) = T^(g)(N_i)` and
`T^(g+1)(M_i) ≠ T^(g+1)(N_i)`.

`g ≥ 4`: parity gadgets (`Parity.conj_ge_four`); `g = 1, 2, 3`: explicit rank-3 sparse paving
matroids (`Low1`, `Low2`, `Low3`); all padded by `i` loops.

Sanity lemmas: `genusTutte 1` is the ordinary Tutte polynomial (source p. 3), and the source's
specialization identity `T^(g)(M) = 2^{-|E|} T^(g+1)(M)|_{…=2}` holds when every variable of a slot
involving `A_{g+1}` is set to `2`.
-/

open MvPolynomial Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace GenusTutte

/-- **MathDB 361823 (Miezaki–Oura–Sakuma–Shinohara, Conjecture 5.12)**, the review's endpoint. -/
theorem miezaki_conj_5_12 (g : ℕ) (hg : 0 < g) :
    ∃ (n : ℕ → ℕ) (M N : ∀ i, Matroid (Fin (n i))) (hM : ∀ i, (M i).E = Set.univ)
      (hN : ∀ i, (N i).E = Set.univ),
      StrictMono n ∧ ∀ i, genusTutte g (M i) (hM i) = genusTutte g (N i) (hN i) ∧
        genusTutte (g + 1) (M i) (hM i) ≠ genusTutte (g + 1) (N i) (hN i) := by
  match g, hg with
  | 1, _ => exact Low1.conj_one
  | 2, _ => exact Low2.conj_two
  | 3, _ => exact Low3.conj_three
  | s + 4, _ => exact Parity.conj_ge_four s

theorem miezaki_conj_5_12' (g : ℕ) (hg : 0 < g) : MiezakiConj512 g := miezaki_conj_5_12 g hg

/-! ## Sanity lemma 1: genus 1 is the Tutte polynomial -/

/-- The Tutte polynomial `T(M; x, y) = Σ_{A ⊆ E} (x-1)^{ρ(E)-ρ(A)} (y-1)^{|A|-ρ(A)}` (source p. 3),
with `x = X false`, `y = X true`. -/
noncomputable def tutte {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (_hE : M.E = Set.univ) : MvPolynomial Bool ℤ :=
  ∑ A : Finset α, (X false - 1) ^ ((M.eRk Set.univ).toNat - (M.eRk (A : Set α)).toNat) *
    (X true - 1) ^ (A.card - (M.eRk (A : Set α)).toNat)

theorem genusTutte_one {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) :
    genusTutte 1 M hE = rename (fun b => ((Sum.inl 0 : Slot 1), b)) (tutte M hE) := by
  unfold genusTutte tutte
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Finset α)) _ _ fun A => ?_
  rw [Fintype.prod_eq_single (Sum.inl 0)]
  · simp [slotSet, Equiv.funUnique]
  · intro s hs
    rcases s with i | ⟨p, b⟩
    · exact absurd (by rw [Subsingleton.elim i 0]) hs
    · exact absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)

/-! ## Sanity lemma 2: the specialization identity -/

/-- Slots of genus `g` inside genus `g + 1` (those not involving `A_{g+1}`). -/
def slotEmb (g : ℕ) : Slot g → Slot (g + 1)
  | Sum.inl i => Sum.inl (Fin.castSucc i)
  | Sum.inr (p, c) => Sum.inr (⟨(Fin.castSucc p.1.1, Fin.castSucc p.1.2),
      Fin.castSucc_lt_castSucc_iff.2 p.2⟩, c)

theorem slotEmb_injective (g : ℕ) : Function.Injective (slotEmb g) := by
  rintro (i | ⟨p, c⟩) (j | ⟨q, d⟩) h <;> simp [slotEmb] at h
  · rw [h]
  · obtain ⟨⟨h1, h2⟩, rfl⟩ := h
    have : p = q := Subtype.ext (Prod.ext h1 h2)
    rw [this]

/-- The substitution: variables of slots not involving `A_{g+1}` go to the genus-`g` variables, all
others (`x, y` of `A_{g+1}`, of every `A_j ∩ A_{g+1}` and of every `A_j ∪ A_{g+1}`) to `2`. -/
noncomputable def specVar (g : ℕ) : Slot (g + 1) × Bool → MvPolynomial (Slot g × Bool) ℤ
  | (Sum.inl i, b) => if h : (i : ℕ) < g then X (Sum.inl ⟨i, h⟩, b) else 2
  | (Sum.inr (p, c), b) =>
      if h : (p.1.2 : ℕ) < g then
        X (Sum.inr (⟨(⟨p.1.1, lt_trans p.2 h⟩, ⟨p.1.2, h⟩), p.2⟩, c), b)
      else 2

theorem specVar_emb (g : ℕ) (s : Slot g) (b : Bool) : specVar g (slotEmb g s, b) = X (s, b) := by
  rcases s with i | ⟨p, c⟩
  · simp [slotEmb, specVar]
  · simp [slotEmb, specVar, p.1.2.2]

theorem specVar_not_emb (g : ℕ) (s : Slot (g + 1)) (hs : s ∉ Set.range (slotEmb g)) (b : Bool) :
    specVar g (s, b) = 2 := by
  rcases s with i | ⟨p, c⟩
  · simp only [specVar]
    split_ifs with h
    · exact (hs ⟨Sum.inl ⟨i, h⟩, by simp [slotEmb]⟩).elim
    · rfl
  · simp only [specVar]
    split_ifs with h
    · exact (hs ⟨Sum.inr (⟨(⟨p.1.1, lt_trans p.2 h⟩, ⟨p.1.2, h⟩), p.2⟩, c), by simp [slotEmb]⟩).elim
    · rfl

theorem slotSet_slotEmb {α : Type*} [DecidableEq α] (g : ℕ) (A : Fin (g + 1) → Finset α)
    (s : Slot g) : slotSet A (slotEmb g s) = slotSet (Fin.init A) s := by
  rcases s with i | ⟨p, c⟩
  · rfl
  · cases c <;> rfl

/-- **Specialization identity** (source p. 4, with every variable of a slot involving `A_{g+1}` set
to `2`): `2^{|E|} T^(g)(M) = T^(g+1)(M)|_{…=2}`. -/
theorem specialization {α : Type*} [Fintype α] [DecidableEq α] (g : ℕ) (M : Matroid α)
    (hE : M.E = Set.univ) :
    aeval (specVar g) (genusTutte (g + 1) M hE) = (2 ^ Fintype.card α : ℤ) • genusTutte g M hE := by
  rw [genusTutte_eq_gt, genusTutte_eq_gt]
  set ρ : Finset α → ℕ := fun B => (M.eRk (B : Set α)).toNat
  set R := (M.eRk Set.univ).toNat
  -- each summand specializes to the genus-`g` summand of the initial `g` probes
  have hterm : ∀ A : Fin (g + 1) → Finset α, aeval (specVar g) (term (g + 1) ρ R A) =
      term g ρ R (Fin.init A) := by
    intro A
    unfold term
    rw [map_prod]
    rw [← Finset.prod_subset (Finset.subset_univ (univ.map ⟨slotEmb g, slotEmb_injective g⟩))]
    · rw [Finset.prod_map]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [Function.Embedding.coeFn_mk, map_mul, map_pow, map_sub, aeval_X, map_one,
        specVar_emb, slotSet_slotEmb]
    · intro s _ hs
      have hs' : s ∉ Set.range (slotEmb g) := by
        rintro ⟨s', rfl⟩
        exact hs (Finset.mem_map_of_mem _ (mem_univ s'))
      simp only [map_mul, map_pow, map_sub, aeval_X, map_one, specVar_not_emb g s hs']
      norm_num
  unfold gt
  rw [map_sum]
  simp only [hterm]
  let e : (Fin (g + 1) → Finset α) ≃ (Fin g → Finset α) × Finset α :=
    { toFun := fun A => (Fin.init A, A (Fin.last g))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := fun A => Fin.snoc_init_self A
      right_inv := fun p => by simp }
  rw [Fintype.sum_equiv e (fun A => term g ρ R (Fin.init A)) (fun p => term g ρ R p.1)
    (fun A => rfl), Fintype.sum_prod_type]
  simp only [Finset.sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [zsmul_eq_mul]
  push_cast
  ring

end GenusTutte

/-! ## Endpoint report (printed by the build) -/

#check @GenusTutte.miezaki_conj_5_12
#print GenusTutte.genusTutte
#print GenusTutte.Slot
#print GenusTutte.slotSet
#print GenusTutte.MiezakiConj512
#check @GenusTutte.genusTutte_one
#check @GenusTutte.specialization
#print axioms GenusTutte.miezaki_conj_5_12
#print axioms GenusTutte.miezaki_conj_5_12'
#print axioms GenusTutte.genusTutte_one
#print axioms GenusTutte.specialization
#print axioms GenusTutte.Parity.conj_ge_four
#print axioms GenusTutte.Parity.rigidity
#print axioms GenusTutte.Low1.conj_one
#print axioms GenusTutte.Low2.conj_two
#print axioms GenusTutte.Low3.conj_three
```

### `GTSanity.lean`

```lean
import GTMain

/-!
# The specialization identity as printed in the source is a misprint

Source p. 4 prints `T^(g)(M) = 2^{-|E_M|} T^(g+1)(M)|_{x_{A_{g+1}}=2, y_{A_{g+1}}=2, x_{A_j∩A_{g+1}}=2, y_{A_k∪A_{g+1}}=2}`,
leaving `y_{A_j∩A_{g+1}}` and `x_{A_k∪A_{g+1}}` free. Taken literally this fails already for `g = 1` and the
one-element matroid consisting of a loop: at the point where all remaining variables are `3` the left side
(times `2^{|E|} = 2`) is `6` and the right side is `8`. `GTMain.specialization` proves the identity with
*every* variable of a slot involving `A_{g+1}` set to `2`, which is evidently what is meant.
-/

open MvPolynomial Finset

set_option linter.unusedSimpArgs false

namespace GenusTutte

namespace Sanity

/-- The matroid on one element that is a loop (no non-loops, `r = 1`, no circuit-hyperplanes). -/
def loopSP : SP (Fin 1) where
  N := ∅
  r := 1
  H := ∅
  hr := le_rfl
  hsub := by simp
  hcard := by simp
  hinter := by simp

theorem loopSP_rank (B : Finset (Fin 1)) : loopSP.rank B = 0 := by
  simp [SP.rank, loopSP]

/-- Which genus-2 variables the printed substitution sets to `2`: `x, y` of `A₂`, `x` of `A₁ ∩ A₂` and
`y` of `A₁ ∪ A₂`. -/
def printed : Slot 2 × Bool → Bool
  | (Sum.inl i, _) => decide (i = 1)
  | (Sum.inr (_, c), b) => c == b

/-- The printed substitution for `g = 1`. -/
noncomputable def printedVar (v : Slot 2 × Bool) : MvPolynomial (Slot 2 × Bool) ℤ :=
  if printed v then 2 else X v

/-- Genus-1 variables viewed among the genus-2 variables. -/
def emb1 (v : Slot 1 × Bool) : Slot 2 × Bool := (slotEmb 1 v.1, v.2)

theorem genusTutte_loop (h : ℕ) :
    genusTutte h loopSP.matroid loopSP.matroid_E = gt h (fun _ : Finset (Fin 1) => 0) 0 := by
  have : loopSP.rank = fun _ => 0 := funext loopSP_rank
  rw [SP.genusTutte_eq, this]

/-- **The literal printed identity fails** (for `g = 1` and a single loop). -/
theorem printed_identity_false :
    aeval printedVar (genusTutte 2 loopSP.matroid loopSP.matroid_E) ≠
      (2 ^ Fintype.card (Fin 1) : ℤ) • rename emb1 (genusTutte 1 loopSP.matroid loopSP.matroid_E) := by
  intro h
  have h3 := congrArg (MvPolynomial.eval (fun _ : Slot 2 × Bool => (3 : ℤ))) h
  rw [genusTutte_loop, genusTutte_loop] at h3
  simp only [gt, term, map_sum, map_prod, map_mul, map_pow, map_sub, map_one, aeval_X, eval_X,
    printedVar, apply_ite (MvPolynomial.eval _), eval_rename, map_ofNat, smul_eq_mul, map_zsmul,
    Function.comp, emb1, Nat.sub_zero, pow_zero, one_mul, zsmul_eq_mul, map_mul, map_pow,
    map_natCast, map_intCast, Fintype.card_fin, Int.cast_pow, Int.cast_ofNat] at h3
  norm_num at h3
  revert h3
  decide +kernel

end Sanity

#print axioms GenusTutte.Sanity.printed_identity_false

end GenusTutte
```

