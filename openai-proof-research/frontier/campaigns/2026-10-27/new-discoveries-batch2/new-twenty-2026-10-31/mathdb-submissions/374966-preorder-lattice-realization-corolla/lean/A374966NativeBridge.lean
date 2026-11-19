import C374966Main
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Finset.Grade

/-!
# MathDB 374966 — independent reviewer audit module (NOT one of the five canonical modules)

Binds the native definitions of Athanasiadis–Chapoton, arXiv:2605.26916v1, to the canonical
replayed endpoint `C374966.conj81_false_at_corolla`:

* §2.3: a finite poset is *graded* if all maximal chains have the same length `d` (length is one
  less than cardinality); "rank `n`" means `d = n`.  Maximal chains are Mathlib's literal
  `IsMaxChain (· ≤ ·)` (a chain not strictly contained in another chain).
* the rank function of a graded poset (Stanley EC1 §3.1, cited as [Sta11]): `0` on minimal
  elements and `+1` along every cover relation (§8 writes `ρ : P → ℕ`).

No `BoundedOrder`, `IsGradedRank` or `GradeOrder` is assumed in the native endpoint.
-/

namespace A374966

open C374966

universe u v

/-- Native §2.3 at rank `n`: every maximal chain has length `n`, i.e. exactly `n + 1` elements. -/
def NativeGradedRank (α : Type v) [PartialOrder α] (n : ℕ) : Prop :=
  ∀ s : Set α, IsMaxChain (· ≤ ·) s → s.ncard = n + 1

/-- Rank function of a graded poset: `0` on minimal elements, `+1` along covers. -/
structure IsNativeRankFn {α : Type v} [PartialOrder α] (ρ : α → ℕ) : Prop where
  min_zero : ∀ a : α, IsMin a → ρ a = 0
  cover_succ : ∀ a b : α, a ⋖ b → ρ b = ρ a + 1

/-- In a finite poset every cover-additive map is strictly monotone. -/
theorem strictMono_of_cover {α : Type v} [PartialOrder α] [Finite α] {ρ : α → ℕ}
    (hc : ∀ a b : α, a ⋖ b → ρ b = ρ a + 1) : StrictMono ρ := by
  have key : ∀ b : α, ∀ a : α, a < b → ρ a < ρ b := by
    intro b
    induction b using WellFoundedLT.induction with
    | ind b ih =>
      intro a hab
      obtain ⟨c, ⟨hac, hcb⟩, hmax⟩ :=
        (wellFounded_gt (α := α)).has_min {x | a ≤ x ∧ x < b}
          ⟨a, show a ≤ a ∧ a < b from ⟨le_rfl, hab⟩⟩
      have hcov : c ⋖ b := by
        refine ⟨hcb, ?_⟩
        intro d hcd hdb
        exact hmax d ⟨hac.trans hcd.le, hdb⟩ hcd
      rw [hc c b hcov]
      rcases eq_or_lt_of_le hac with rfl | hlt
      · omega
      · have := ih c hcb a hlt
        omega
  exact fun a b h => key b a h

/-- Uniqueness of the rank function on a finite poset. -/
theorem rankFn_unique {α : Type v} [PartialOrder α] [Finite α] {ρ ρ' : α → ℕ}
    (h : IsNativeRankFn ρ) (h' : IsNativeRankFn ρ') : ρ = ρ' := by
  funext a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    by_cases hmin : IsMin a
    · rw [h.min_zero a hmin, h'.min_zero a hmin]
    · obtain ⟨b, hb⟩ := not_isMin_iff.1 hmin
      obtain ⟨c, ⟨hbc, hca⟩, hmax⟩ :=
        (wellFounded_gt (α := α)).has_min {x | b ≤ x ∧ x < a}
          ⟨b, show b ≤ b ∧ b < a from ⟨le_rfl, hb⟩⟩
      have hcov : c ⋖ a := by
        refine ⟨hca, ?_⟩
        intro d hcd hda
        exact hmax d ⟨hbc.trans hcd.le, hda⟩ hcd
      rw [h.cover_succ c a hcov, h'.cover_succ c a hcov, ih c hca]

/-- A nonempty finite chain has a greatest element. -/
theorem chain_exists_greatest {α : Type v} [PartialOrder α] [Finite α] {s : Set α}
    (hs : IsChain (· ≤ ·) s) (hne : s.Nonempty) : ∃ t ∈ s, ∀ y ∈ s, y ≤ t := by
  obtain ⟨t, ht, hmax⟩ := (wellFounded_gt (α := α)).has_min s hne
  refine ⟨t, ht, fun y hy => ?_⟩
  by_contra h
  exact hmax y hy ((hs.not_le hy ht).1 h)

/-- The greatest element of a maximal chain is a maximal element of the poset. -/
theorem isMax_of_greatest {α : Type v} [PartialOrder α] {s : Set α}
    (hs : IsMaxChain (· ≤ ·) s) {t : α} (htop : ∀ y ∈ s, y ≤ t) : IsMax t := by
  intro z hz
  have hch : IsChain (· ≤ ·) (insert z s) :=
    hs.1.insert fun b hb _ => Or.inr ((htop b hb).trans hz)
  have e1 := hs.2 hch (Set.subset_insert z s)
  have hzs : z ∈ s := by
    rw [e1]
    exact Set.mem_insert z s
  exact htop z hzs

/-- Counting a maximal chain with a rank function: if `t` is the greatest element of the
maximal chain `s`, then `#s = ρ t + 1` (the chain meets every rank `0, …, ρ t` exactly once). -/
theorem ncard_maxChain {α : Type v} [PartialOrder α] [Finite α] {ρ : α → ℕ}
    (hr : IsNativeRankFn ρ) {s : Set α} (hs : IsMaxChain (· ≤ ·) s) {t : α} (ht : t ∈ s)
    (htop : ∀ y ∈ s, y ≤ t) : s.ncard = ρ t + 1 := by
  have hmono : StrictMono ρ := strictMono_of_cover hr.cover_succ
  have hinj : Set.InjOn ρ s := by
    intro x hx y hy hxy
    by_contra hne
    rcases hs.1 hx hy hne with h | h
    · have := hmono (lt_of_le_of_ne h hne)
      omega
    · have := hmono (lt_of_le_of_ne h (Ne.symm hne))
      omega
  obtain ⟨m, hm, hmmin⟩ := (wellFounded_lt (α := α)).has_min s ⟨t, ht⟩
  have hmle : ∀ y ∈ s, m ≤ y := fun y hy => by
    by_contra h
    exact hmmin y hy ((hs.1.not_le hm hy).1 h)
  have hmisMin : IsMin m := by
    intro z hz
    by_contra hmz
    have hzm : z < m := lt_of_le_of_ne hz (fun h => hmz (le_of_eq h.symm))
    have hch : IsChain (· ≤ ·) (insert z s) :=
      hs.1.insert fun b hb _ => Or.inl (hz.trans (hmle b hb))
    have e1 := hs.2 hch (Set.subset_insert z s)
    have hzs : z ∈ s := by
      rw [e1]
      exact Set.mem_insert z s
    exact hmmin z hzs hzm
  have hsurj : ∀ k, k ≤ ρ t → ∃ x ∈ s, ρ x = k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨m, hm, hr.min_zero m hmisMin⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hx, hxk⟩ := ih (by omega)
      have hxt : x < t := lt_of_le_of_ne (htop x hx) (by rintro rfl; omega)
      obtain ⟨d, ⟨hds, hxd⟩, hdmin⟩ :=
        (wellFounded_lt (α := α)).has_min {y | y ∈ s ∧ x < y}
          ⟨t, show t ∈ s ∧ x < t from ⟨ht, hxt⟩⟩
      have hdle : ∀ b ∈ s, x < b → d ≤ b := fun b hb hxb => by
        by_contra h
        exact hdmin b ⟨hb, hxb⟩ ((hs.1.not_le hds hb).1 h)
      have hcov : x ⋖ d := by
        refine ⟨hxd, ?_⟩
        intro e hxe hed
        have hch : IsChain (· ≤ ·) (insert e s) := by
          refine hs.1.insert fun b hb _ => ?_
          by_cases hbx : b ≤ x
          · exact Or.inr (hbx.trans hxe.le)
          · exact Or.inl (hed.le.trans (hdle b hb ((hs.1.not_le hb hx).1 hbx)))
        have e1 := hs.2 hch (Set.subset_insert e s)
        have hes : e ∈ s := by
          rw [e1]
          exact Set.mem_insert e s
        exact hdmin e ⟨hes, hxe⟩ hed
      exact ⟨d, hds, by rw [hr.cover_succ x d hcov, hxk]⟩
  have himg : ρ '' s = ((Finset.range (ρ t + 1) : Finset ℕ) : Set ℕ) := by
    ext k
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hmono.monotone (htop x hx)
      omega
    · intro hk
      exact hsurj k (by omega)
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset, Finset.card_range]

/-- **Bridge.** Native §2.3 gradedness of rank `n` with its rank function gives the canonical
`IsGradedRank ρ n` (for any bounded-order structure on the same order). -/
theorem isGradedRank_of_native {α : Type v} [PartialOrder α] [Finite α] [BoundedOrder α]
    {ρ : α → ℕ} {n : ℕ} (hg : NativeGradedRank α n) (hr : IsNativeRankFn ρ) :
    IsGradedRank ρ n where
  strictMono := strictMono_of_cover hr.cover_succ
  covBy := hr.cover_succ
  bot := hr.min_zero ⊥ isMin_bot
  top := by
    obtain ⟨M, hM, -⟩ := (IsChain.empty : IsChain (α := α) (· ≤ ·) ∅).exists_maxChain
    have h1 := hg M hM
    have h2 := ncard_maxChain hr hM hM.top_mem (fun y _ => le_top)
    omega

/-- **Converse bridge.** The canonical `IsGradedRank ρ n` gives native gradedness and the
native rank function. -/
theorem native_of_isGradedRank {α : Type v} [PartialOrder α] [Finite α] [BoundedOrder α]
    {ρ : α → ℕ} {n : ℕ} (hg : IsGradedRank ρ n) :
    NativeGradedRank α n ∧ IsNativeRankFn ρ := by
  have hr : IsNativeRankFn ρ :=
    ⟨fun a ha => by rw [isMin_iff_eq_bot.1 ha]; exact hg.bot, hg.covBy⟩
  refine ⟨fun s hs => ?_, hr⟩
  rw [ncard_maxChain hr hs hs.top_mem (fun y _ => le_top), hg.top]

theorem native_iff_isGradedRank {α : Type v} [PartialOrder α] [Finite α] [BoundedOrder α]
    {ρ : α → ℕ} {n : ℕ} : (NativeGradedRank α n ∧ IsNativeRankFn ρ) ↔ IsGradedRank ρ n :=
  ⟨fun h => isGradedRank_of_native h.1 h.2, native_of_isGradedRank⟩

/-! ### The corolla side: `P_τ` is natively graded of rank 3 with rank function `rk` -/

theorem rk_isNativeRankFn : IsNativeRankFn rk where
  min_zero a ha := by
    have h1 : a = botP := le_antisymm (ha (botP_le a)) (botP_le a)
    rw [h1]
    exact rk_botP
  cover_succ _ _ h := rk_covBy h

/-- `rk` is the only rank function of `P_τ`, so `Mtri P rk` is the native `M_{P_τ}`. -/
theorem rk_unique (ρ : P → ℕ) (h : IsNativeRankFn ρ) : ρ = rk :=
  rankFn_unique h rk_isNativeRankFn

/-- Every maximal chain of `P_τ` has exactly four elements (native §2.3, rank 3). -/
theorem P_nativeGraded : NativeGradedRank P 3 := by
  intro s hs
  have hb : botP ∈ s := by
    have hch : IsChain (· ≤ ·) (insert botP s) := hs.1.insert fun b _ _ => Or.inl (botP_le b)
    have e1 := hs.2 hch (Set.subset_insert botP s)
    rw [e1]
    exact Set.mem_insert botP s
  obtain ⟨t, ht, htop⟩ := chain_exists_greatest hs.1 ⟨botP, hb⟩
  rw [ncard_maxChain rk_isNativeRankFn hs ht htop,
    rk_of_maximal t (fun b hb' => le_antisymm (isMax_of_greatest hs htop hb') hb')]

/-! ### Native literal endpoints -/

/-- **Native literal endpoint.** Conjecture 8.1 fails at the corolla `t₃` (`n = 3`) with the
source's own §2.3 gradedness (all maximal chains have four elements) and rank function; no
bounded order, `IsGradedRank` or `GradeOrder` is assumed.  Derived from the canonical
endpoint `C374966.conj81_false_at_corolla` through the bridge. -/
theorem conj81_false_at_corolla_native :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : Fintype L) (_ : DecidableEq L) (_ : DecidableLE L)
      (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      NativeGradedRank L 3 ∧ IsNativeRankFn ρ ∧
        transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, ρ, hg, hr, h⟩
  obtain ⟨M, hM, -⟩ := (IsChain.empty : IsChain (α := L) (· ≤ ·) ∅).exists_maxChain
  have hM4 : M.ncard = 3 + 1 := hg M hM
  obtain ⟨x, -⟩ := Set.nonempty_of_ncard_ne_zero (s := M) (by omega)
  have : Nonempty L := ⟨x⟩
  let _ : BoundedOrder L := Fintype.toBoundedOrder L
  exact conj81_false_at_corolla
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ρ, isGradedRank_of_native hg hr, h⟩

/-- The native endpoint with the (unused) zeta conjunct on the same lattice. -/
theorem conj81_false_at_corolla_native_with_zeta
    (Zeta : ∀ (L : Type u) [Lattice L] [Fintype L], Prop) :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : Fintype L) (_ : DecidableEq L) (_ : DecidableLE L)
      (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      NativeGradedRank L 3 ∧ IsNativeRankFn ρ ∧ Zeta L ∧
        transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, ρ, hg, hr, -, h⟩
  exact conj81_false_at_corolla_native
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ, hg, hr, h⟩

/-! ### Non-vacuity on standard finite lattices (hypotheses derived, not assumed) -/

/-- The four-element chain `Fin 4` with rank `Fin.val`. -/
theorem fin4_rankFn : IsNativeRankFn (fun a : Fin 4 => (a : ℕ)) where
  min_zero a ha := by
    have h0 : a = ⊥ := isMin_iff_eq_bot.1 ha
    subst h0
    rfl
  cover_succ a b h := by
    show (b : ℕ) = (a : ℕ) + 1
    have h1 : (a : ℕ) < b := h.1
    have hb4 : (b : ℕ) < 4 := b.2
    by_contra hne
    have h2 : (a : ℕ) + 1 < b := by omega
    have hc4 : (a : ℕ) + 1 < 4 := by omega
    exact h.2 (show a < (⟨(a : ℕ) + 1, hc4⟩ : Fin 4) from Nat.lt_succ_self _)
      (show (⟨(a : ℕ) + 1, hc4⟩ : Fin 4) < b from h2)

theorem fin4_nativeGraded : NativeGradedRank (Fin 4) 3 := fun s hs => by
  rw [ncard_maxChain fin4_rankFn hs hs.top_mem (fun y _ => le_top)]
  rfl

theorem fin4_isGradedRank : IsGradedRank (fun a : Fin 4 => (a : ℕ)) 3 :=
  isGradedRank_of_native fin4_nativeGraded fin4_rankFn

/-- The Boolean lattice `B₃ = Finset (Fin 3)` with rank `card`. -/
theorem boolean3_rankFn : IsNativeRankFn (fun s : Finset (Fin 3) => s.card) where
  min_zero s hs := by
    have h0 : s = ⊥ := isMin_iff_eq_bot.1 hs
    subst h0
    rfl
  cover_succ s t h := by
    obtain ⟨a, ha, rfl⟩ := Finset.covBy_iff_exists_insert.1 h
    exact Finset.card_insert_of_notMem ha

theorem boolean3_nativeGraded : NativeGradedRank (Finset (Fin 3)) 3 := fun s hs => by
  rw [ncard_maxChain boolean3_rankFn hs hs.top_mem (fun y _ => le_top)]
  decide

theorem boolean3_isGradedRank : IsGradedRank (fun s : Finset (Fin 3) => s.card) 3 :=
  isGradedRank_of_native boolean3_nativeGraded boolean3_rankFn

#print axioms conj81_false_at_corolla_native
#print axioms conj81_false_at_corolla_native_with_zeta
#print axioms isGradedRank_of_native
#print axioms native_of_isGradedRank
#print axioms native_iff_isGradedRank
#print axioms ncard_maxChain
#print axioms strictMono_of_cover
#print axioms rankFn_unique
#print axioms chain_exists_greatest
#print axioms isMax_of_greatest
#print axioms rk_isNativeRankFn
#print axioms rk_unique
#print axioms P_nativeGraded
#print axioms fin4_rankFn
#print axioms fin4_nativeGraded
#print axioms fin4_isGradedRank
#print axioms boolean3_rankFn
#print axioms boolean3_nativeGraded
#print axioms boolean3_isGradedRank

end A374966
