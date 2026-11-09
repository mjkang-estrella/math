import SelectedEntropy333569
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort

namespace MathDB333569
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

/-- Selections with prescribed inclusion/exclusion correspond exactly to
arbitrary selections of the remaining coordinates. -/
def freeSelectionEquiv {A : Type*} [Fintype A] [DecidableEq A]
    (I O : Finset A) (hIO : Disjoint I O) :
    {S : Finset A // I ⊆ S ∧ Disjoint O S} ≃
      Finset {i : A // i ∉ I ∧ i ∉ O} where
  toFun S := univ.filter (fun i => i.val ∈ S.val)
  invFun T := ⟨I ∪ T.image Subtype.val, by
    constructor
    · exact subset_union_left
    · apply disjoint_left.mpr
      intro i hiO hi
      rcases mem_union.mp hi with hiI | hiT
      · exact disjoint_left.mp hIO hiI hiO
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp hiT
        exact j.property.2 hiO⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro (hi | ⟨j,hj,rfl⟩)
      · exact S.property.1 hi
      · exact hj
    · intro hi
      by_cases hiI : i ∈ I
      · exact Or.inl hiI
      · right
        have hiO : i ∉ O := fun h => disjoint_left.mp S.property.2 h hi
        exact ⟨⟨i,hiI,hiO⟩,hi,rfl⟩
  right_inv T := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · rintro (hiI | ⟨j,hj,hji⟩)
      · exact False.elim (i.property.1 hiI)
      · have he : j = i := Subtype.ext hji
        exact he ▸ hj
    · intro hi
      exact Or.inr ⟨i,hi,rfl⟩

theorem card_freeSelections {A : Type*} [Fintype A] [DecidableEq A]
    (I O : Finset A) (hIO : Disjoint I O) :
    Fintype.card {S : Finset A // I ⊆ S ∧ Disjoint O S} =
      2 ^ (Fintype.card A - (I ∪ O).card) := by
  rw [Fintype.card_congr (freeSelectionEquiv I O hIO), Fintype.card_finset]
  congr 1
  calc
    _ = Fintype.card {i : A // i ∉ I ∪ O} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp))
    _ = _ := by
      rw [Fintype.card_subtype_compl]
      rw [Fintype.card_coe]

/-- Consecutive selected endpoints have no selected coordinate between them. -/
def ConsecutiveSelection {N : ℕ} (a b : Fin N) (S : Finset (Fin N)) : Prop :=
  a ∈ S ∧ b ∈ S ∧ ∀ c ∈ Finset.Ioo a b, c ∉ S

theorem card_consecutiveSelections {N : ℕ} (a b : Fin N) (hab : a < b) :
    Fintype.card {S : Finset (Fin N) // ConsecutiveSelection a b S} =
      2 ^ (N - (b.val-a.val+1)) := by
  classical
  let I : Finset (Fin N) := {a,b}
  let O : Finset (Fin N) := Finset.Ioo a b
  have hd : Disjoint I O := by
    apply disjoint_left.mpr
    intro c hc hcO
    simp only [I, mem_insert, mem_singleton] at hc
    simp only [O, mem_Ioo] at hcO
    rcases hc with rfl | rfl
    · exact (lt_irrefl _ hcO.1)
    · exact (lt_irrefl _ hcO.2)
  have he : (fun S => ConsecutiveSelection a b S) =
      (fun S => I ⊆ S ∧ Disjoint O S) := by
    funext S
    apply propext
    simp only [ConsecutiveSelection, I, insert_subset_iff, singleton_subset_iff, O, disjoint_left]
    tauto
  have hc : Fintype.card {S : Finset (Fin N) // ConsecutiveSelection a b S} =
      Fintype.card {S : Finset (Fin N) // I ⊆ S ∧ Disjoint O S} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun S => by exact (congrFun he S).to_iff))
  rw [hc, card_freeSelections I O hd]
  congr 1
  have hu : I ∪ O = Finset.Icc a b := by
    ext c
    simp only [I, O, mem_union, mem_insert, mem_singleton, mem_Ioo, mem_Icc]
    constructor
    · rintro ((rfl | rfl) | ⟨h₁,h₂⟩)
      · exact ⟨le_rfl,hab.le⟩
      · exact ⟨hab.le,le_rfl⟩
      · exact ⟨h₁.le,h₂.le⟩
    · rintro ⟨h₁,h₂⟩
      by_cases hca : c = a
      · exact Or.inl (Or.inl hca)
      by_cases hcb : c = b
      · exact Or.inl (Or.inr hcb)
      exact Or.inr ⟨lt_of_le_of_ne h₁ (Ne.symm hca),lt_of_le_of_ne h₂ hcb⟩
  rw [hu]
  simp only [Fintype.card_fin, Fin.card_Icc]
  omega


/-- The adjacency list of an increasing enumeration is precisely the set of
consecutive selected pairs. This is the finite combinatorial entropy bridge. -/
theorem sum_consecutive_enumeration {N d : ℕ} (S : Finset (Fin N))
    (e : Fin (d+1) ≃o S) (f : Fin N → Fin N → ℝ) :
    (∑ a : Fin N, ∑ b : Fin N,
      if a < b ∧ ConsecutiveSelection a b S then f a b else 0) =
      ∑ j : Fin d, f (e j.castSucc).val (e j.succ).val := by
  classical
  let T : Finset (Fin N × Fin N) := univ.filter
    (fun p => p.1 < p.2 ∧ ConsecutiveSelection p.1 p.2 S)
  have hpair : ∀ j : Fin d,
      (e j.castSucc).val < (e j.succ).val ∧
        ConsecutiveSelection (e j.castSucc).val (e j.succ).val S := by
    intro j
    refine ⟨e.strictMono Fin.castSucc_lt_succ, (e _).property, (e _).property, ?_⟩
    intro c hc hcS
    have hc := mem_Ioo.mp hc
    let q := e.symm ⟨c,hcS⟩
    have hq : e q = ⟨c,hcS⟩ := e.apply_symm_apply _
    have h₁ : j.castSucc < q := (e.lt_iff_lt).mp (by
      change (e j.castSucc).val < (e q).val
      rw [hq]; exact hc.1)
    have h₂ : q < j.succ := (e.lt_iff_lt).mp (by
      change (e q).val < (e j.succ).val
      rw [hq]; exact hc.2)
    have : j.val < q.val ∧ q.val < j.val+1 := ⟨h₁,h₂⟩
    omega
  have hsum : (∑ p ∈ T, f p.1 p.2) = ∑ j : Fin d, f (e j.castSucc).val (e j.succ).val := by
    symm
    apply Finset.sum_bij (fun j _ => ((e j.castSucc).val,(e j.succ).val))
    · intro j _; exact mem_filter.mpr ⟨mem_univ _,hpair j⟩
    · intro i _ j _ hij
      have heq : e i.castSucc = e j.castSucc := Subtype.ext (congrArg Prod.fst hij)
      have := e.injective heq
      exact Fin.castSucc_inj.mp this
    · intro p hp
      obtain ⟨hab,ha,hb,hmid⟩ := (mem_filter.mp hp).2
      let u := e.symm ⟨p.1,ha⟩
      let v := e.symm ⟨p.2,hb⟩
      have huv : u < v := (e.lt_iff_lt).mp (by simpa [u,v] using hab)
      have hv : v.val = u.val+1 := by
        by_contra hh
        have hg : u.val+1 < v.val := by omega
        let q : Fin (d+1) := ⟨u.val+1,by omega⟩
        have hq₁ : p.1 < (e q).val := by
          have := e.strictMono (show u < q by change u.val < u.val+1; omega)
          change (e u).val < (e q).val at this
          simpa [u] using this
        have hq₂ : (e q).val < p.2 := by
          have := e.strictMono (show q < v from hg)
          change (e q).val < (e v).val at this
          simpa [v] using this
        exact hmid _ (mem_Ioo.mpr ⟨hq₁,hq₂⟩) (e q).property
      let j : Fin d := ⟨u.val,by omega⟩
      have hju : j.castSucc = u := Fin.ext rfl
      have hjv : j.succ = v := Fin.ext (by dsimp [j]; omega)
      refine ⟨j,mem_univ _,?_⟩
      rw [hju,hjv]
      simp [u,v]
    · intro j _; rfl
  rw [← hsum]
  simp only [T, sum_filter]
  exact (Fintype.sum_prod_type (fun p : Fin N × Fin N =>
    if p.1 < p.2 ∧ ConsecutiveSelection p.1 p.2 S then f p.1 p.2 else 0)).symm

theorem sampleEntropy_pairs {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (n : ℕ) (S : Finset (Fin (n+1))) :
    sampleEntropy (chart l t) n S =
      (if S.Nonempty then initialEntropy (chart l t) else 0) +
      ∑ a : Fin (n+1), ∑ b : Fin (n+1),
        if a < b ∧ ConsecutiveSelection a b S then
          conditionalEntropy (l ^ (b.val-a.val)) t else 0 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (card_pos.mpr hS))
    let e : Fin (d+1) ≃o S := S.orderIsoOfFin hd
    rw [sampleEntropy_selected hl hl1 ht ht1 n d S e.toEquiv e.strictMono,
      ite_eq_left hS, sum_consecutive_enumeration S e]
    congr 1
    apply sum_congr rfl
    intro j _
    change conditionalEntropy (l ^ (((e j.succ).val.val : ℤ) - (e j.castSucc).val.val).toNat) t = _
    congr 2
    omega
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [sampleEntropy_empty (chart_mem_interior hl hl1 ht ht1)]
    simp [ConsecutiveSelection]


theorem sum_indicator {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] (c : ℝ) :
    (∑ a : A, if P a then c else 0) = (Fintype.card {a : A // P a} : ℝ) * c := by
  classical
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast (Fintype.card_subtype P).symm

/-- Exact uniform-subset entropy sum in endpoint-pair form. The exponent counts
free outside coordinates; no asymptotic statement is used. -/
theorem sum_sampleEntropy_pairs {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (n : ℕ) :
    (∑ S : Finset (Fin (n+1)), sampleEntropy (chart l t) n S) =
      ((2:ℝ)^(n+1)-1) * initialEntropy (chart l t) +
      ∑ a : Fin (n+1), ∑ b : Fin (n+1), if a < b then
        (2:ℝ)^((n+1)-(b.val-a.val+1)) * conditionalEntropy (l^(b.val-a.val)) t else 0 := by
  classical
  simp_rw [sampleEntropy_pairs hl hl1 ht ht1 n]
  rw [sum_add_distrib]
  congr 1
  · have hh := sum_indicator (fun S : Finset (Fin (n+1)) => S.Nonempty) (initialEntropy (chart l t))
    have hcompat : (∑ S : Finset (Fin (n+1)), if S.Nonempty then initialEntropy (chart l t) else 0) =
        (Fintype.card {S : Finset (Fin (n+1)) // S.Nonempty} : ℝ) * initialEntropy (chart l t) := by
      convert hh using 1
    apply hcompat.trans
    have hc : Fintype.card {S : Finset (Fin (n+1)) // S.Nonempty} = 2^(n+1)-1 := by
      have he : (fun S : Finset (Fin (n+1)) => S.Nonempty) = (fun S => S ≠ ∅) := by
        funext S; exact propext nonempty_iff_ne_empty
      have hcard := Fintype.card_subtype_compl (fun S : Finset (Fin (n+1)) => S = ∅)
      have heq := Fintype.card_congr (Equiv.subtypeEquivRight (fun S => (congrFun he S).to_iff))
      rw [heq, hcard]
      simp [Fintype.card_finset]
    rw [hc, Nat.cast_sub (by have h : 0 < (2:ℕ)^(n+1) := Nat.pow_pos (by decide); omega), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  · rw [Finset.sum_comm]
    apply sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro b _
    by_cases hab : a < b
    · simp only [hab, true_and, ite_eq_left]
      have hh := sum_indicator (ConsecutiveSelection a b) (conditionalEntropy (l^(b.val-a.val)) t)
      rw [hh, card_consecutiveSelections a b hab]
      simp
    · simp [hab]

end
end MathDB333569
