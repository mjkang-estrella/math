import Mathlib
open Finset
namespace Majority
variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
variable (E : R → S → Bool)
def row (i : R) : Finset S := univ.filter (fun j => E i j = true)
def col (j : S) : Finset R := univ.filter (fun i => E i j = false)
def dr (i : R) := (row E i).card
def ds (j : S) := (col E j).card
omit [DecidableEq R] [DecidableEq S] in
lemma total : (∑ i, dr E i) + (∑ j, ds E j) = Fintype.card R * Fintype.card S := by
  simp only [dr, ds, row, col, card_filter]
  rw [sum_comm (f := fun j i => if E i j = false then 1 else 0), ← sum_add_distrib]
  simp only [← sum_add_distrib]
  have h (i : R) (j : S) : (if E i j = true then 1 else 0) + (if E i j = false then 1 else 0) = (1 : ℕ) := by cases E i j <;> simp
  simp only [h, sum_const, card_univ, smul_eq_mul, mul_one]
omit [DecidableEq R] [DecidableEq S] in
lemma pair_bound (hr : 0 < Fintype.card R) (hs : Fintype.card R ≤ Fintype.card S) :
    ∃ i j, Fintype.card R ≤ dr E i + ds E j := by
  classical
  have : Nonempty R := Fintype.card_pos_iff.mp hr
  have : Nonempty S := Fintype.card_pos_iff.mp (lt_of_lt_of_le hr hs)
  obtain ⟨i, _, hi⟩ := univ.exists_max_image (dr E) univ_nonempty
  obtain ⟨j, _, hj⟩ := univ.exists_max_image (ds E) univ_nonempty
  refine ⟨i,j,?_⟩
  by_contra hn
  have ha : (∑ x, dr E x) ≤ Fintype.card R * dr E i := by
    calc _ ≤ ∑ _x : R, dr E i := sum_le_sum (fun x _ => hi x (mem_univ x))
         _ = _ := by simp
  have hb : (∑ y, ds E y) ≤ Fintype.card S * ds E j := by
    calc _ ≤ ∑ _y : S, ds E j := sum_le_sum (fun y _ => hj y (mem_univ y))
         _ = _ := by simp
  have hc : dr E i ≤ Fintype.card S := card_le_card (filter_subset _ _)
  have ht := total E
  have hprod : Fintype.card R * (dr E i + ds E j) ≤ Fintype.card S * (dr E i + ds E j) := Nat.mul_le_mul_right _ hs
  nlinarith
omit [DecidableEq R] [DecidableEq S] in
lemma pair_strict (hr : 0 < Fintype.card R) (hs : Fintype.card R < Fintype.card S)
    (he : ∃ i j, E i j = true) :
    ∃ i j, Fintype.card R + 1 ≤ dr E i + ds E j := by
  classical
  have : Nonempty R := Fintype.card_pos_iff.mp hr
  have : Nonempty S := Fintype.card_pos_iff.mp (lt_trans hr hs)
  obtain ⟨i, _, hi⟩ := univ.exists_max_image (dr E) univ_nonempty
  obtain ⟨j, _, hj⟩ := univ.exists_max_image (ds E) univ_nonempty
  obtain ⟨u,v,huv⟩ := he
  have hpos : 0 < dr E i := by
    have hv : v ∈ row E u := by simp [row, huv]
    have hdu : 0 < dr E u := card_pos.mpr ⟨v,hv⟩
    exact lt_of_lt_of_le hdu (hi u (mem_univ u))
  refine ⟨i,j,?_⟩
  by_contra hn
  have ha : (∑ x, dr E x) ≤ Fintype.card R * dr E i := by
    calc _ ≤ ∑ _x : R, dr E i := sum_le_sum (fun x _ => hi x (mem_univ x))
         _ = _ := by simp
  have hb : (∑ y, ds E y) ≤ Fintype.card S * ds E j := by
    calc _ ≤ ∑ _y : S, ds E j := sum_le_sum (fun y _ => hj y (mem_univ y))
         _ = _ := by simp
  have ht := total E
  have hp : Fintype.card R * dr E i < Fintype.card S * dr E i := Nat.mul_lt_mul_of_pos_right hs hpos
  have hq : Fintype.card S * (dr E i + ds E j) ≤ Fintype.card S * Fintype.card R := Nat.mul_le_mul_left _ (by omega)
  nlinarith

def arc : R ⊕ S → R ⊕ S → Prop
  | .inl i, .inr j => E i j = true
  | .inr j, .inl i => E i j = false
  | _, _ => False
noncomputable def cover (T : Finset (R ⊕ S)) : Finset (R ⊕ S) :=
  by classical exact univ.filter (fun v => v ∈ T ∨ ∃ u ∈ T, arc E u v)
lemma mem_cover (T : Finset (R ⊕ S)) (v) :
    v ∈ cover E T ↔ v ∈ T ∨ ∃ u ∈ T, arc E u v := by
  classical
  simp [cover]
lemma self_cover (T : Finset (R ⊕ S)) : T ⊆ cover E T := by
  intro v hv
  exact (mem_cover E T v).mpr (Or.inl hv)
lemma cover_mono {T U : Finset (R ⊕ S)} (h : T ⊆ U) : cover E T ⊆ cover E U := by
  intro v hv
  rcases (mem_cover E T v).mp hv with hv | ⟨u,hu,ha⟩
  · exact (mem_cover E U v).mpr (Or.inl (h hv))
  · exact (mem_cover E U v).mpr (Or.inr ⟨u,h hu,ha⟩)
lemma pair_card (i : R) (j : S) :
    (cover E {Sum.inl i, Sum.inr j}).card = dr E i + ds E j + 1 := by
  classical
  have hh : cover E {Sum.inl i, Sum.inr j} =
      (insert i (col E j)).disjSum (insert j (row E i)) := by
    ext v
    cases v <;> simp [mem_cover, mem_disjSum, col, row, arc]
  rw [hh, card_disjSum]
  cases he : E i j <;> simp [col, row, dr, ds, card_insert_of_notMem, he, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma extend (T : Finset (R ⊕ S)) (h k : ℕ)
    (hh : h ≤ Fintype.card R + Fintype.card S) (hk : T.card ≤ k)
    (hc : h + T.card ≤ (cover E T).card + k) :
    ∃ U : Finset (R ⊕ S), U.card ≤ k ∧ h ≤ (cover E U).card := by
  classical
  by_cases hd : h ≤ (cover E T).card
  · exact ⟨T,hk,hd⟩
  have hroom : h - (cover E T).card ≤ (univ \ cover E T).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_sum]
    omega
  obtain ⟨X,hX,hXcard⟩ := exists_subset_card_eq hroom
  refine ⟨T ∪ X, ?_, ?_⟩
  · have := card_union_le T X
    omega
  · have hdis : Disjoint (cover E T) X := by
      rw [disjoint_left]
      intro v hv hx
      exact (mem_sdiff.mp (hX hx)).2 hv
    have hsub : cover E T ∪ X ⊆ cover E (T ∪ X) := by
      intro v hv
      rcases mem_union.mp hv with hv | hv
      · exact cover_mono E subset_union_left hv
      · exact self_cover E _ (mem_union_right T hv)
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdis] at hcard
    omega

lemma empty_cover : cover E ∅ = ∅ := by
  classical
  ext v
  simp [mem_cover]
lemma sink_cover (T : Finset (R ⊕ S)) :
    (cover (fun (_ : R) (_ : S) => false) T).card ≤ Fintype.card R + T.card := by
  classical
  have hh : cover (fun (_ : R) (_ : S) => false) T ⊆
      (univ : Finset R).image Sum.inl ∪ T := by
    intro v hv
    rcases (mem_cover _ T v).mp hv with hv | ⟨u,hu,ha⟩
    · exact mem_union_right _ hv
    · cases v with
      | inl i => exact mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
      | inr j => cases u <;> simp [arc] at ha
  calc _ ≤ _ := card_le_card hh
       _ ≤ ((univ : Finset R).image (Sum.inl : R → R ⊕ S)).card + T.card := card_union_le _ _
       _ = _ := by rw [card_image_of_injective _ Sum.inl_injective, card_univ]
lemma sink_upper (hr : 0 < Fintype.card R) (hs : Fintype.card R < Fintype.card S)
    (he : ¬ ∃ i j, E i j = true) :
    ∃ T : Finset (R ⊕ S), T.card ≤ (Fintype.card S - Fintype.card R + 1) / 2 ∧
      (Fintype.card R + Fintype.card S + 1) / 2 ≤ (cover E T).card := by
  classical
  let k := (Fintype.card S - Fintype.card R + 1) / 2
  by_cases hk : k = 0
  · have heq : Fintype.card R = Fintype.card S := by dsimp [k] at hk; omega
    have : False := by omega
    exact this.elim
  obtain ⟨X,_,hX⟩ := (univ : Finset S).exists_subset_card_eq (show k ≤ Fintype.card S by dsimp [k]; omega)
  have hne : X.Nonempty := card_pos.mp (by omega)
  let T : Finset (R ⊕ S) := X.image Sum.inr
  have hT : T.card = k := by dsimp [T]; rw [card_image_of_injective _ Sum.inr_injective, hX]
  have hcov : cover E T = (univ : Finset R).disjSum X := by
    ext v
    cases v with
    | inl i =>
      obtain ⟨j,hj⟩ := hne
      have hij : E i j = false := by cases h : E i j <;> simp_all
      have hv : Sum.inl i ∈ cover E T :=
        (mem_cover E T _).mpr (Or.inr ⟨Sum.inr j,mem_image.mpr ⟨j,hj,rfl⟩,
          show arc E (Sum.inr j) (Sum.inl i) from hij⟩)
      simpa only [Finset.inl_mem_disjSum, Finset.mem_univ, iff_true] using hv
    | inr j => simp [mem_cover,T,arc]
  refine ⟨T,by omega,?_⟩
  rw [hcov, card_disjSum, card_univ, hX]
  dsimp [k]
  omega

lemma upper (hr : 0 < Fintype.card R) (hs : Fintype.card R ≤ Fintype.card S) :
    ∃ T : Finset (R ⊕ S),
      T.card ≤ max 2 ((Fintype.card S - Fintype.card R + 1) / 2) ∧
      (Fintype.card R + Fintype.card S + 1) / 2 ≤ (cover E T).card := by
  classical
  let r := Fintype.card R
  let s := Fintype.card S
  let k := max 2 ((s-r+1)/2)
  let h := (r+s+1)/2
  have hh : h ≤ r+s := by dsimp [h,r,s]; omega
  by_cases hd : s ≤ r+2
  · obtain ⟨i,j,hij⟩ := pair_bound E hr hs
    refine ⟨{Sum.inl i, Sum.inr j},?_,?_⟩
    · simp only [card_insert_of_notMem (by simp : Sum.inl i ∉ ({Sum.inr j} : Finset (R ⊕ S))), card_singleton]
      exact le_max_left _ _
    · rw [pair_card]
      dsimp [r,s] at hd
      omega
  · by_cases he : ∃ i j, E i j = true
    · obtain ⟨i,j,hij⟩ := pair_strict E hr (by dsimp [r,s] at hd; omega) he
      have hc : ({Sum.inl i, Sum.inr j} : Finset (R ⊕ S)).card = 2 := by simp
      apply extend E {Sum.inl i,Sum.inr j} h k hh
      · rw [hc]; exact le_max_left _ _
      · rw [hc, pair_card]
        have hk : (s-r+1)/2 ≤ k := le_max_right _ _
        dsimp [h,r,s] at *
        omega
    · obtain ⟨T,hT,hcov⟩ := sink_upper E hr (by dsimp [r,s] at hd; omega) he
      exact ⟨T,le_trans hT (le_max_right _ _),hcov⟩

-- A direct finite-set definition of the source minimum: all finite subsets
-- of the vertex set are allowed; coverage uses the closed out-neighborhood.
lemma gamma_exists (E : R → S → Bool) : ∃ k : ℕ, ∃ T : Finset (R ⊕ S), T.card ≤ k ∧
      (Fintype.card R + Fintype.card S + 1)/2 ≤ (cover E T).card := by
  classical
  refine ⟨Fintype.card R + Fintype.card S, univ,?_,?_⟩
  · simp
  · have hself := card_le_card (self_cover E (univ : Finset (R ⊕ S)))
    simp only [card_univ, Fintype.card_sum] at hself
    omega
noncomputable def gamma (E : R → S → Bool) : ℕ := by
  classical
  exact Nat.find (gamma_exists E)
lemma gamma_le_iff (k : ℕ) : gamma E ≤ k ↔
    ∃ T : Finset (R ⊕ S), T.card ≤ k ∧
      (Fintype.card R + Fintype.card S + 1)/2 ≤ (cover E T).card := by
  classical
  constructor
  · intro h
    have hw : ∃ T : Finset (R ⊕ S), T.card ≤ gamma E ∧
      (Fintype.card R + Fintype.card S + 1)/2 ≤ (cover E T).card := by exact Nat.find_spec (gamma_exists E)
    obtain ⟨U,hU,hc⟩ := hw
    exact ⟨U,le_trans hU h,hc⟩
  · exact fun h => Nat.find_min' (gamma_exists E) h
noncomputable def DOM : ℕ := by
  classical
  exact (univ : Finset (R → S → Bool)).sup (fun E => gamma E)
lemma le_DOM : gamma E ≤ (DOM (R := R) (S := S) : ℕ) := by
  classical
  exact le_sup (f := fun E : R → S → Bool => gamma E) (mem_univ E)
lemma DOM_upper (hr : 0 < Fintype.card R) (hs : Fintype.card R ≤ Fintype.card S) :
    (DOM (R := R) (S := S) : ℕ) ≤ max 2 ((Fintype.card S-Fintype.card R+1)/2) := by
  classical
  unfold DOM
  apply Finset.sup_le
  intro E _
  exact (gamma_le_iff E _).mpr (upper E hr hs)

lemma gamma_pos (hr : 0 < Fintype.card R) : 0 < gamma E := by
  classical
  by_contra hn
  have hz : gamma E ≤ 0 := by omega
  obtain ⟨T,hT,hc⟩ := (gamma_le_iff E 0).mp hz
  have hzero : T = ∅ := card_eq_zero.mp (by omega)
  rw [hzero, empty_cover, card_empty] at hc
  omega
lemma sink_lower (hs : Fintype.card R ≤ Fintype.card S) :
    (Fintype.card S - Fintype.card R + 1)/2 ≤ gamma (fun (_ : R) (_ : S) => false) := by
  have hw := (gamma_le_iff (fun (_ : R) (_ : S) => false) _).mp (le_refl _)
  obtain ⟨T,hT,hc⟩ := hw
  have hb := sink_cover T
  omega

/-- Exact Conjecture 4.10, with DOM defined as the maximum over every
orientation of K_{r,s} and gamma as the minimum over every vertex subset. -/
theorem exact_formula (hr : 0 < Fintype.card R) (hs : Fintype.card R ≤ Fintype.card S)
    (hne : DOM (R := R) (S := S) ≠ 1) :
    DOM (R := R) (S := S) = if Fintype.card S ≤ Fintype.card R + 2 then 2
      else (Fintype.card S - Fintype.card R + 1)/2 := by
  have hu := DOM_upper (R := R) (S := S) hr hs
  have hl : 1 ≤ DOM (R := R) (S := S) := le_trans (gamma_pos (fun (_ : R) (_ : S) => false) hr)
    (le_DOM (fun (_ : R) (_ : S) => false))
  have hb := le_trans (sink_lower (R := R) (S := S) hs) (le_DOM (fun (_ : R) (_ : S) => false))
  split_ifs with hd
  · have hk : (Fintype.card S-Fintype.card R+1)/2 ≤ 2 := by omega
    rw [max_eq_left hk] at hu
    omega
  · have hk : 2 ≤ (Fintype.card S-Fintype.card R+1)/2 := by omega
    rw [max_eq_right hk] at hu
    omega
/-- The usual orientation condition for the complete bipartite graph:
no arcs inside either part and exactly one arc on each cross pair. -/
def IsOrientation (A : (R ⊕ S) → (R ⊕ S) → Prop) : Prop :=
  (∀ i i', ¬ A (.inl i) (.inl i')) ∧ (∀ j j', ¬ A (.inr j) (.inr j')) ∧
  (∀ i j, A (.inl i) (.inr j) ↔ ¬ A (.inr j) (.inl i))
omit [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S] in
lemma arc_orientation : IsOrientation (arc E) := by
  refine ⟨by simp [arc],by simp [arc],?_⟩
  intro i j
  cases E i j <;> simp [arc, *]
omit [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S] in
lemma orientation_representation (A : (R ⊕ S) → (R ⊕ S) → Prop)
    (hA : IsOrientation A) : ∃ E : R → S → Bool, arc E = A := by
  classical
  refine ⟨fun i j => decide (A (.inl i) (.inr j)),?_⟩
  funext u v
  apply propext
  rcases hA with ⟨hR,hS,hC⟩
  cases u with
  | inl i => cases v with
    | inl i' => simp [arc,hR]
    | inr j => simp [arc]
  | inr j => cases v with
    | inl i => simp [arc,hC]
    | inr j' => simp [arc,hS]
lemma majority_criterion (T : Finset (R ⊕ S)) :
    (Fintype.card R + Fintype.card S + 1)/2 ≤ (cover E T).card ↔
      Fintype.card R + Fintype.card S ≤ 2 * (cover E T).card := by omega
lemma gamma_minimum :
    (∃ T : Finset (R ⊕ S), T.card = gamma E ∧
      Fintype.card R + Fintype.card S ≤ 2 * (cover E T).card) ∧
    (∀ T : Finset (R ⊕ S), Fintype.card R + Fintype.card S ≤ 2 * (cover E T).card →
      gamma E ≤ T.card) := by
  have hw := (gamma_le_iff E _).mp (le_refl _)
  obtain ⟨T,hT,hcov⟩ := hw
  have hmin : ∀ T : Finset (R ⊕ S), Fintype.card R + Fintype.card S ≤ 2 * (cover E T).card →
      gamma E ≤ T.card := by
    intro U hU
    exact (gamma_le_iff E _).mpr ⟨U,le_refl _,(majority_criterion E U).mpr hU⟩
  exact ⟨⟨T,le_antisymm hT (hmin T ((majority_criterion E T).mp hcov)),
    (majority_criterion E T).mp hcov⟩,hmin⟩
lemma DOM_maximum :
    (∃ E : R → S → Bool, gamma E = DOM (R := R) (S := S)) ∧
      (∀ E : R → S → Bool, gamma E ≤ DOM (R := R) (S := S)) := by
  classical
  obtain ⟨E,_,hE⟩ := exists_mem_eq_sup (univ : Finset (R → S → Bool)) univ_nonempty gamma
  exact ⟨⟨E,hE.symm⟩,fun E => le_DOM E⟩

/-- Natural-number spelling of the exact MathDB formula. -/
theorem mathdb_326640 (r s : ℕ) (hr : 0 < r) (hrs : r ≤ s)
    (hne : DOM (R := Fin r) (S := Fin s) ≠ 1) :
    DOM (R := Fin r) (S := Fin s) = if s ≤ r + 2 then 2 else (s-r+1)/2 := by
  simpa only [Fintype.card_fin] using
    (exact_formula (R := Fin r) (S := Fin s) (by simpa) (by simpa) hne)
lemma ceiling_spelling (r s : ℕ) :
    s-r ≤ 2*((s-r+1)/2) ∧ 2*((s-r+1)/2) < s-r+2 := by omega
#print axioms mathdb_326640
#print axioms orientation_representation
#print axioms gamma_minimum
#print axioms DOM_maximum
end Majority
